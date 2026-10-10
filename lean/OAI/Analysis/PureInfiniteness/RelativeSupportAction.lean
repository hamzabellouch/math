import Mathlib

namespace OAI

/-! Relations on a positive support element extend to positive elements below
it. This is the finite support calculation needed to combine abelian-range
maps in the norm ultrapower. -/

noncomputable section

namespace WeakPureInfiniteness

variable {D : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma mul_eq_zero_of_positive_le {x y : D} (hx : 0 ≤ x) (hxy : x ≤ y)
    (b : D) (hby : b * y = 0) : b * x = 0 := by
  have hconj : b * x * star b = 0 := by
    apply le_antisymm
    · calc
        _ ≤ b * y * star b := star_right_conjugate_le_conjugate hxy b
        _ = 0 := by rw [hby, zero_mul]
    · exact star_right_conjugate_nonneg hx b
  have hs : IsSelfAdjoint (CFC.sqrt x) := (CFC.sqrt_nonneg x).isSelfAdjoint
  have hroot : b * CFC.sqrt x = 0 := by
    apply (CStarRing.mul_star_self_eq_zero_iff _).mp
    calc
      _ = b * (CFC.sqrt x * CFC.sqrt x) * star b := by
        simp only [star_mul, hs.star_eq, mul_assoc]
      _ = 0 := by rw [CFC.sqrt_mul_sqrt_self x, hconj]
  calc
    b * x = (b * CFC.sqrt x) * CFC.sqrt x := by rw [mul_assoc, CFC.sqrt_mul_sqrt_self x]
    _ = 0 := by rw [hroot, zero_mul]

lemma mul_eq_self_of_positive_le {x y : D} (hx : 0 ≤ x) (hxy : x ≤ y)
    (b : D) (hby : b * y = y) : b * x = x := by
  let j := Unitization.inrNonUnitalStarAlgHom ℂ D
  have he : ((b : Unitization ℂ D) - 1) * (y : Unitization ℂ D) = 0 := by
    simp only [sub_mul, one_mul, ← Unitization.inr_mul, hby, sub_self]
  have hz := mul_eq_zero_of_positive_le (D := Unitization ℂ D)
    (show 0 ≤ (x : Unitization ℂ D) from map_nonneg j hx)
    (Unitization.inr_mono hxy) ((b : Unitization ℂ D) - 1) he
  have hbx : (b : Unitization ℂ D) * (x : Unitization ℂ D) = (x : Unitization ℂ D) :=
    sub_eq_zero.mp (by simpa only [sub_mul, one_mul] using hz)
  have hh : ((b * x : D) : Unitization ℂ D) = (x : Unitization ℂ D) := by
    simpa only [Unitization.inr_mul] using hbx
  exact Unitization.inr_injective hh

end WeakPureInfiniteness

end

end OAI
