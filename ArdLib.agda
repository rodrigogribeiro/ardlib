-- A simple formalization of a library for
-- controling Arduino using dependent types to
-- ensure safety.

module ArdLib where

open import Category.Monad
open import Category.Monad.State

open import Data.Nat
open import Data.Fin
open import Data.Product

open import Function

module ArduinoData where

      -- Defining pins

      data Mode : Set where
        write read : Mode

      -- A is the value that can be read or written in a pin

      data Pin (A : Set) : Mode → Set where
        pin : ∀ m → A → Pin A m

      -- setting pins mode

      setMode : ∀ {A m} → (n : Mode) → Pin A m → Pin A n
      setMode n (pin _ v) = pin n v

      -- reading and writing data in a pin

      -- first, we define a type function to describe the type
      -- of operations over pins, indexed by their current mode

      El : ∀ {A m} → Pin A m → Set
      El {A} {write} _ = A → Pin A write
      El {A} {read} _ = A

      -- now, the function for using pins can be described using El family

      use : ∀ {A m} → (p : Pin A m) → El p
      use {A} {write} p             = λ v → pin write v
      use {A} {read}  (pin .read v) = v

      -- In order to avoid access to a invalid pin,
      -- I will use something like a vector. I could not use
      -- a vector, because it is a heterogeneous list (it can mix pins
      -- in read or write modes).

      data Pins (A : Set) : ℕ → Set where
        ε : Pins A 0
        _,_ : ∀ {m n} → Pin A m → Pins A n → Pins A (suc n)

      infixr 4 _,_

      -- looking up a pin. Using this function is impossible to access an invalid pin

      lookup : ∀ {A : Set} {n} → Fin n → Pins A n → ∃ (λ m → Pin A m)
      lookup zero (_,_ {m} (pin .m x) ps) = m , pin m x
      lookup (suc i) (p , ps)             = lookup i ps 

      -- monad definitions

module ArduinoMonad (A : Set)(n : ℕ) where

    open ArduinoData

    Ard : Set
    Ard = Pins A n

    ArdM : Set → Set
    ArdM = State Ard

    open RawMonadState (StateMonadState Ard) public

    -- lifting operations to monad

    lookupM : Fin n → ArdM (∃ (λ m → Pin A m))
    lookupM i = get >>= return ∘ lookup i

    ElM : ∀ {m} → Pin A m → Set
    ElM {write} _ = A → ArdM (Pin A write)
    ElM {read}  _ = ArdM A

    useM : ∀ {m} → (p : Pin A m) → ElM p
    useM {write} p = λ v → (return (pin write v))
    useM {read}  p = return (use p)

    -- syntax facilities

    bind : ∀ {A B} → ArdM A → (A → ArdM B) → ArdM B
    bind = _>>=_

    syntax bind m (\ x → c) = ⟨ x ← m ⟩ c 

    


    
    
