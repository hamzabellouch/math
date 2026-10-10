import OAI.NumberTheory.Ostmann.QuadraticCenter.InverseWeylRational

namespace OAI

namespace Ostmann.QuadraticCenter
open Finset

theorem same_quotient_gap {L i j : ℕ} (hL : 0 < L) (hij : i/L=j/L) :
    |(i:ℤ)-(j:ℤ)| ≤ ((L-1:ℕ):ℤ) := by
  have hi := Nat.mod_add_div i L
  have hj := Nat.mod_add_div j L
  have him := Nat.mod_lt i hL
  have hjm := Nat.mod_lt j hL
  rw [hij] at hi
  apply abs_le.mpr
  constructor <;> omega

theorem rational_block_spacing (theta : ℝ) (b : ℤ) (r : ℕ) (hr : 0 < r)
    (hcop : Int.gcd (r:ℤ) b = 1)
    (happrox : |theta-(b:ℝ)/r| ≤ 1/(r:ℝ)^2)
    (i j : ℕ) (hij : i ≠ j) (hquot : i/(r/2+1)=j/(r/2+1)) (m : ℤ) :
    1/(2*(r:ℝ)) ≤ |theta*((i:ℝ)+1)-theta*((j:ℝ)+1)-m| := by
  have hgap := same_quotient_gap (Nat.zero_lt_succ (r/2)) hquot
  have hrdiv : 2*(((r/2+1-1:ℕ):ℤ)) ≤ (r:ℤ) := by omega
  have hshort : 2*|((i+1:ℕ):ℤ)-((j+1:ℕ):ℤ)| ≤ (r:ℤ) := by
    norm_num only [Int.natCast_add, Int.natCast_one, add_sub_add_right_eq_sub]
    omega
  have had : ((i+1:ℕ):ℤ) ≠ ((j+1:ℕ):ℤ) := by exact_mod_cast Nat.succ_ne_succ_iff.mpr hij
  have h := approximated_multiples_spacing theta b r hr hcop happrox
    ((i+1:ℕ):ℤ) ((j+1:ℕ):ℤ) m had hshort
  simpa only [Int.cast_add, Int.cast_one, Int.cast_natCast, Nat.cast_add, Nat.cast_one] using h

end Ostmann.QuadraticCenter

end OAI
