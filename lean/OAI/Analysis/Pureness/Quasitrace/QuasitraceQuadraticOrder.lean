import OAI.Analysis.Pureness.Quasitrace.QuasitraceMetricContinuity
import Mathlib.Tactic.Module

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma selfAdjoint_le_quadratic (z : D) (hz : IsSelfAdjoint z) (r : ℝ) (hr : 0 < r) :
    z ≤ r • (1 : D)+r⁻¹ • (star z*z) := by
  have he : r • (1 : D)+r⁻¹ • (star z*z)-z =
      r⁻¹ • (star (z-(r/2) • 1)*(z-(r/2) • 1))+(3*r/4) • 1 := by
    simp only [star_sub,star_smul,star_trivial,star_one,hz.star_eq,sub_mul,mul_sub,
      smul_mul_assoc,mul_smul_comm,mul_one,one_mul]
    match_scalars <;> field_simp <;> ring
  apply sub_nonneg.mp
  rw [he]
  exact add_nonneg (smul_nonneg (inv_nonneg.mpr hr.le) (star_mul_self_nonneg _))
    (smul_nonneg (by positivity) zero_le_one)

namespace PositiveQuasitrace
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))
include hsqrt

lemma sqrt_le_add_quadratic_error (a b : Positive D) (r : ℝ) (hr : 0 < r) :
    Real.sqrt (T a) ≤ Real.sqrt (T b)+
      Real.sqrt (r*T ⟨1,zero_le_one⟩+r⁻¹*T (Positive.starMul (a.1-b.1))) := by
  let u : ℝ≥0 := ⟨r,hr.le⟩
  let v : ℝ≥0 := ⟨r⁻¹,inv_nonneg.mpr hr.le⟩
  let e := Positive.add (Positive.smul u (⟨1,zero_le_one⟩ : Positive D))
    (Positive.smul v (Positive.starMul (a.1-b.1)))
  have ho : a ≤ Positive.add b e := by
    change a.1 ≤ b.1+(r • (1 : D)+r⁻¹ • (star (a.1-b.1)*(a.1-b.1)))
    have h := selfAdjoint_le_quadratic (a.1-b.1) (a.2.isSelfAdjoint.sub b.2.isSelfAdjoint) r hr
    exact (sub_le_iff_le_add.mp h).trans_eq (add_comm _ _)
  have he : T e = r*T ⟨1,zero_le_one⟩+r⁻¹*T (Positive.starMul (a.1-b.1)) := by
    rw [T.map_add_commute _ _ (((Commute.one_left (star (a.1-b.1)*(a.1-b.1))).smul_left (u : ℝ)).smul_right (v : ℝ)),T.map_smul,T.map_smul]
    rfl
  exact (Real.sqrt_le_sqrt (T.monotone ho)).trans (by simpa only [he] using hsqrt b e)

lemma sqrt_sub_abs_le_quadratic (a b : Positive D) (r : ℝ) (hr : 0 < r) :
    |Real.sqrt (T a)-Real.sqrt (T b)| ≤
      Real.sqrt (r*T ⟨1,zero_le_one⟩+r⁻¹*T (Positive.starMul (a.1-b.1))) := by
  have hab := T.sqrt_le_add_quadratic_error hsqrt a b r hr
  have hba := T.sqrt_le_add_quadratic_error hsqrt b a r hr
  have he : Positive.starMul (b.1-a.1) = Positive.starMul (a.1-b.1) := by
    apply Subtype.ext
    change star (b.1-a.1)*(b.1-a.1) = star (a.1-b.1)*(a.1-b.1)
    rw [show b.1-a.1 = -(a.1-b.1) from by abel,star_neg,neg_mul_neg]
  rw [he] at hba
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩
end PositiveQuasitrace
end CuntzPureness

end

end OAI
