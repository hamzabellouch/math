import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationKernel

namespace OAI

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
namespace TamingCompatibility.Concentration
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [InnerProductSpace ℝ V] in
lemma cutKernel_tsupport (η : V → ℝ) (r : ℝ) : tsupport (cutKernel η r) ⊆ tsupport η :=
  tsupport_mul_subset_left

omit [InnerProductSpace ℝ V] in
lemma cutKernel_nonneg (η : V → ℝ) (hη : ∀ z, 0 ≤ η z) (r : ℝ) (z : V) :
    0 ≤ cutKernel η r z := mul_nonneg (hη z) (rationalKernel_nonneg r z)

omit [InnerProductSpace ℝ V] in
lemma cutKernel_le (η : V → ℝ) (hη : ∀ z, η z ≤ 1) (r : ℝ) (z : V) :
    cutKernel η r z ≤ rationalKernel r z := mul_le_of_le_one_left (rationalKernel_nonneg r z) (hη z)

omit [InnerProductSpace ℝ V] in
lemma rationalKernel_away {r a : ℝ} (ha : 0 < a) {z : V} (hz : a ≤ ‖z‖) :
    rationalKernel r z ≤ r^4/a^6 := by
  unfold rationalKernel
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hh : a^2 ≤ r^2+‖z‖^2 := by nlinarith [sq_nonneg r,norm_nonneg z]
  have hp := pow_le_pow_left₀ (sq_nonneg a) hh 3
  simpa only [←pow_mul] using hp

lemma bump_derivative_away_bound (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) {a : ℝ} (ha : 0 < a)
    (hηone : ∀ z, ‖z‖ < a → η z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, ∀ z w : V,
      |fderiv ℝ η z w*rationalKernel r z| ≤ C*r^4*‖w‖ := by
  obtain ⟨B,hB,hbound⟩ := compact_continuous_bound (fderiv ℝ η)
    (hη.continuous_fderiv (by simp)) (hηc.fderiv ℝ)
  refine ⟨B/a^6,by positivity,fun r z w => ?_⟩
  by_cases hz : ‖z‖ < a
  · have he : η =ᶠ[𝓝 z] (fun _ => 1) := by
      filter_upwards [continuous_norm.continuousAt.preimage_mem_nhds (gt_mem_nhds hz)] with y hy
      exact hηone y hy
    rw [he.fderiv_eq]
    simp only [fderiv_fun_const]
    change |(0 : ℝ)*rationalKernel r z| ≤ _
    rw [zero_mul,abs_zero]
    positivity
  · have hder : |fderiv ℝ η z w| ≤ B*‖w‖ :=
      (ContinuousLinearMap.le_opNorm _ w).trans (mul_le_mul_of_nonneg_right (hbound z) (norm_nonneg _))
    rw [abs_mul,abs_of_nonneg (rationalKernel_nonneg r z)]
    calc
      _ ≤ (B*‖w‖)*(r^4/a^6) := mul_le_mul hder (rationalKernel_away ha (le_of_not_gt hz))
        (rationalKernel_nonneg r z) (by positivity)
      _ = _ := by ring

lemma cutKernel_deriv_bound (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    {a : ℝ} (ha : 0 < a) (hηone : ∀ z, ‖z‖ < a → η z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ z w : V,
      |fderiv ℝ (cutKernel η r) z w| ≤
        6*radialCoefficient r ‖z‖*|inner ℝ z w| + C*r^4*‖w‖ := by
  obtain ⟨C,hC,hbound⟩ := bump_derivative_away_bound η hη hηc ha hηone
  refine ⟨C,hC,fun r hr z w => ?_⟩
  rw [cutKernel_deriv hr η hη]
  have he : 6*r^4/(r^2+‖z‖^2)^4 = 6*radialCoefficient r ‖z‖ := by unfold radialCoefficient; ring
  rw [he]
  have hp : 0 ≤ 6*radialCoefficient r ‖z‖ := mul_nonneg (by norm_num) (radialCoefficient_nonneg _ _)
  have hm : |η z*(6*radialCoefficient r ‖z‖)*inner ℝ z w| ≤
      6*radialCoefficient r ‖z‖*|inner ℝ z w| := by
    rw [abs_mul,abs_mul,abs_of_nonneg (hη0 z),abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hp (hη1 z)) (abs_nonneg _)
  exact (abs_sub _ _).trans (by linarith [hbound r z w])
end TamingCompatibility.Concentration

end
end

end OAI
