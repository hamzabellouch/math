import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.SparseScalarNodes

namespace OAI

section

namespace KS.W19.SparseScalarNodes
open KS.W01 KS.W15.ComplexMachine

theorem ratLength_div_le (q r : ℚ) : ratLength (q/r) ≤ 4*(ratLength q+ratLength r)+7 := by
  obtain ⟨hn,hd⟩ := rational_parts_le_two_pow_length q
  obtain ⟨rn,rd⟩ := rational_parts_le_two_pow_length r
  obtain ⟨outn,outd⟩ := KS.W30.div_parts_le_two_pow q r (ratLength q) (ratLength r) hn hd rn rd
  have h := ratLength_le_of_parts (q/r) _ _ outn outd
  omega

theorem divNodeTicks_le (q r : ℚ) :
    divNodeTicks q r ≤ 1200000*(ratLength q+ratLength r+1)^3 := by
  have hs := ratLength_div_le q r
  have hp : ratLength q+ratLength r+1 ≤ (ratLength q+ratLength r+1)^3 :=
    Nat.le_self_pow (by decide) _
  simp only [divNodeTicks,divTicks,pairTicks,KS.W30.RationalDivision.inputBits,
    KS.W29.polynomialFuel,List.length_append]
  change 4*ratLength q+2*ratLength r+6 +
    1100000*(ratLength q+ratLength r+1)^3 + (2*ratLength (q/r)+2) ≤ _
  omega

theorem ticks_polynomial (a b : ℚ) :
    ticks a b ≤ 3000000*(200*(ratLength a+ratLength b+1))^3 := by
  have l1 : ratLength (1 : ℚ) = 7 := by decide
  have l2 : ratLength (2 : ℚ) = 9 := by decide
  have la := ratLength_add_le a 1
  have lb := ratLength_mul_le 2 b
  have ln := ratLength_neg_le (a+1)
  rw [l1] at la
  rw [l2] at lb
  let H := 200*(ratLength a+ratLength b+1)
  have h1 : ratLength a+ratLength (1 : ℚ)+1 ≤ H := by rw [l1]; dsimp [H]; omega
  have h2 : ratLength (2 : ℚ)+ratLength b+1 ≤ H := by rw [l2]; dsimp [H]; omega
  have h3 : ratLength (a+1)+1 ≤ H := by dsimp [H]; omega
  have h4 : ratLength (-(a+1))+ratLength (2*b)+1 ≤ H := by dsimp [H]; omega
  have t1 := (addNodeTicks_le a 1).trans (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left h1 3))
  have t2 := (mulNodeTicks_le 2 b).trans (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left h2 3))
  have t3 := (negNodeTicks_le (a+1)).trans (Nat.mul_le_mul_left 1048576 (Nat.pow_le_pow_left h3 3))
  have t4 := (divNodeTicks_le (-(a+1)) (2*b)).trans (Nat.mul_le_mul_left 1200000 (Nat.pow_le_pow_left h4 3))
  have hp : H ≤ H^3 := Nat.le_self_pow (by decide) _
  have hH : 200 ≤ H := by dsimp [H]; omega
  change (encodeRat 1).length+1+((encodeRat 2).length+1+
    (addNodeTicks a 1+(mulNodeTicks 2 b+(negNodeTicks (a+1)+divNodeTicks (-(a+1)) (2*b))))) ≤ 3000000*H^3
  change ratLength (1 : ℚ)+1+(ratLength (2 : ℚ)+1+_) ≤ _
  rw [l1,l2]
  omega

end KS.W19.SparseScalarNodes

end

end OAI
