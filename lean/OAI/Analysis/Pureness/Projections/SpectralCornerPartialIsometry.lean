import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped CStarAlgebra
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem exists_partial_isometry_of_spectral_lower_bound
    (x e : D) (he : IsStarProjection e) (hc : Commute e (star x*x))
    (t : ℝ) (ht : 0 < t) (hl : t • e ≤ e*(star x*x)) :
    ∃ v : D, star v*v=e ∧ v*e=v ∧ ∀ p : D, p*x=x → p*v=v := by
  let a := star x*x
  let s := e*a+(1-e)
  let δ := min t 1
  have hδ : 0 < δ := lt_min ht zero_lt_one
  have hs0 : 0 ≤ s := add_nonneg (Commute.mul_nonneg he.nonneg (star_mul_self_nonneg x) hc)
    he.one_sub.nonneg
  have hbound : δ • (1 : D) ≤ s := by
    calc
      δ • (1 : D) = δ • e + δ • (1-e) := by rw [← smul_add, add_sub_cancel]
      _ ≤ t • e + (1-e) := add_le_add
        (smul_le_smul_of_nonneg_right (min_le_left _ _) he.nonneg)
        (by simpa only [one_smul] using
          smul_le_smul_of_nonneg_right (min_le_right t 1) he.one_sub.nonneg)
      _ ≤ s := add_le_add hl le_rfl
  have hδunit : IsUnit (δ • (1 : D)) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (isUnit_iff_ne_zero.mpr hδ.ne').map (algebraMap ℝ D)
  have hstrict : IsStrictlyPositive s := IsStrictlyPositive.iff_of_unital.mpr
    ⟨hs0, CStarAlgebra.isUnit_of_le _ hbound
      (IsStrictlyPositive.iff_of_unital.mpr ⟨smul_nonneg hδ.le zero_le_one,hδunit⟩)⟩
  let r := s ^ (-(1/2) : ℝ)
  have hrs : IsSelfAdjoint r := (show 0 ≤ r from CFC.rpow_nonneg).isSelfAdjoint
  have hca : a*e=e*a := hc.eq.symm
  have hae : e*a*e=e*a := by
    rw [mul_assoc, hca, ← mul_assoc, he.isIdempotentElem.eq]
  have hse : s*e=e*a := by
    dsimp [s]
    rw [add_mul, hae,
      sub_mul, one_mul, he.isIdempotentElem.eq, sub_self, add_zero]
  have hes : e*s=e*a := by
    dsimp [s]
    rw [mul_add, ← mul_assoc, he.isIdempotentElem.eq,
      mul_sub, mul_one, he.isIdempotentElem.eq, sub_self, add_zero]
  have hec : Commute s e := hse.trans hes.symm
  have hre : Commute r e := hec.cfc_nnreal _
  have hrnorm : r*s*r=1 := CFC.conjugate_rpow_neg_one_half s hstrict
  let v := x*e*r
  have hve : v*e=v := by
    dsimp [v]
    rw [mul_assoc (x*e), hre.eq, ← mul_assoc, mul_assoc x e e, he.isIdempotentElem.eq]
  have hv : star v*v=e := by
    calc
      star v*v = r*(e*a*e)*r := by
        dsimp [v,a]
        simp only [star_mul,hrs.star_eq,he.isSelfAdjoint.star_eq]
        noncomm_ring
      _ = r*(s*e)*r := by rw [hae,hse]
      _ = (r*s)*(e*r) := by simp only [mul_assoc]
      _ = (r*s)*(r*e) := by rw [← hre.eq]
      _ = (r*s*r)*e := by simp only [mul_assoc]
      _ = e := by rw [hrnorm,one_mul]
  refine ⟨v,hv,hve,?_⟩
  intro p hp
  dsimp [v]
  rw [← mul_assoc p, ← mul_assoc p, hp]

theorem partial_isometry_range_projection
    (v e : D) (hve : v*e=v) (hv : star v*v=e)
    (p : D) (hp : IsStarProjection p) (hpv : p*v=v) :
    IsStarProjection (v*star v) ∧ v*star v ≤ p := by
  have hr : IsStarProjection (v*star v) := ⟨by
    calc
      (v*star v)*(v*star v) = (v*(star v*v))*star v := by simp only [mul_assoc]
      _ = v*star v := by rw [hv,hve], by simp [IsSelfAdjoint]⟩
  refine ⟨hr,(hr.le_iff_mul_eq_right hp).mpr ?_⟩
  rw [← mul_assoc,hpv]
end CuntzPureness

end

end OAI
