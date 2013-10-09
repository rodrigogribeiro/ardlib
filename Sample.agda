module Sample where

open import Data.Nat
open import Data.Fin
open import ArdLib

open ArduinoData
open ArduinoMonad


-- some test cases

p0 : Pin ℕ read
p0 = pin read 0

p1 : Pin ℕ write
p1 = pin write 0 

p2 : Pin ℕ read
p2 = pin read 0

p3 : Pin ℕ write
p3 = pin write 0 

pins : Pins ℕ 4
pins = p0 , p1 , p2 , p3 , ε

four : Fin 4
four = suc (suc (suc zero))

five : Fin 5
five = suc (suc (suc (suc zero)))

-- next line does not type check...

-- g = lookup five pins

g = lookup four pins

-- next line does not type check

-- h = writeData 1 p0

h = writeData 1 p1

test : ArdM ⊤
    test = 
      ⟨p₀ ← get >>= lookupM zero ⟩ 
      ⟨

    if readData p₀ ≡ zero then
      setPinMode p₀ read
    else setPinMode p₀ write
