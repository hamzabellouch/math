import OAI.NumberTheory.Ostmann.Construction.CRTInterpolation

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem stdAddChar_mul_complement (p R : ℕ) [NeZero p] [NeZero R] (k : ℤ) :
    ZMod.stdAddChar ((R:ZMod (p*R))*(k:ZMod (p*R))) =
      ZMod.stdAddChar (k:ZMod p) := by
  have hR : (R:ℂ)≠0 := by exact_mod_cast NeZero.ne R
  have hp : (p:ℂ)≠0 := by exact_mod_cast NeZero.ne p
  have heq : (R:ZMod (p*R))*(k:ZMod (p*R)) = ((R:ℤ)*k:ℤ) := by push_cast; rfl
  rw [heq,ZMod.stdAddChar_coe,ZMod.stdAddChar_coe]
  congr 1
  push_cast
  field_simp

theorem stdAddChar_mul_complement_of_eq (N p R : ℕ)
    [NeZero N] [NeZero p] [NeZero R] (hN : p*R=N) (k : ℤ) :
    ZMod.stdAddChar ((R:ZMod N)*(k:ZMod N)) =
      ZMod.stdAddChar (k:ZMod p) := by
  subst N
  exact stdAddChar_mul_complement p R k

theorem stdAddChar_crt (ι : Type*) [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)] [NeZero (∏ i,p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j))) (z : ZMod (∏ i,p i)) :
    ZMod.stdAddChar z = ∏ i, ZMod.stdAddChar
      (interpolationCoordinate p (ZMod.prodEquivPi p hcop z) i) := by
  rw [← crtReconstruct_eq p hcop z]
  conv_rhs => rw [crtReconstruct_coordinates]
  unfold crtReconstruct
  rw [Supply.addChar_sum_eq_prod]
  apply Finset.prod_congr rfl
  intro i hi
  have hR : otherProduct p i≠0 := by
    intro h
    have hh := mul_otherProduct p i
    rw [h,mul_zero] at hh
    exact NeZero.ne (∏ j,p j) hh.symm
  let : NeZero (otherProduct p i) := ⟨hR⟩
  have h := stdAddChar_mul_complement_of_eq (∏ j,p j) (p i) (otherProduct p i)
    (mul_otherProduct p i)
    ((interpolationCoordinate p (ZMod.prodEquivPi p hcop z) i).val:ℤ)
  simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using h

end Ostmann.Construction

end

end OAI
