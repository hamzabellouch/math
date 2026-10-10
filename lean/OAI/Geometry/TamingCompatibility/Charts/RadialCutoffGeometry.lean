import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ShrinkingCutoff

namespace OAI


noncomputable section
namespace TamingCompatibility
open Set Filter ComplexMatrix EuclideanSobolevOperators
open scoped ContDiff Topology SchwartzMap

namespace GeometricHilbert

lemma normalizedCutoff_bounded_radius (L : Space ≃L[ℝ] Space)
    (χ : 𝓢(Space,ℂ)) (hc : HasCompactSupport (χ : Space → ℂ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : Space, ∀ r : ℝ, ∀ hr : 0 < r,
      tsupport (normalizedCutoff L q r hr.ne' χ) ⊆ Metric.closedBall q (c*r) := by
  obtain ⟨R,hR⟩ := hc.exists_bound_of_continuousOn (f := fun x : Space => x) continuous_id.continuousOn
  let B := max R 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨‖L.symm.toContinuousLinearMap‖*B+1,by positivity,?_⟩
  intro q r hr y hy
  let z := r⁻¹ • L y-r⁻¹ • L q
  have hz : z ∈ tsupport χ := normalizedCutoff_support L q r hr.ne' χ hy
  have hze : ‖z‖ ≤ B := (hR z hz).trans (le_max_left _ _)
  have he : y-q = r • L.symm z := by
    apply L.injective
    simp only [map_sub,map_smul,ContinuousLinearEquiv.apply_symm_apply,z,
      smul_sub,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  rw [Metric.mem_closedBall,dist_eq_norm,he,norm_smul,Real.norm_of_nonneg hr.le]
  calc
    _ ≤ r*(‖L.symm.toContinuousLinearMap‖*‖z‖) :=
      mul_le_mul_of_nonneg_left (L.symm.toContinuousLinearMap.le_opNorm z) hr.le
    _ ≤ r*(‖L.symm.toContinuousLinearMap‖*B) := by gcongr
    _ ≤ _ := by nlinarith

lemma normalizedCutoffs_bounded_radius (L : Space ≃L[ℝ] Space)
    (χ : ℕ → 𝓢(Space,ℂ)) (hc : ∀ n ≤ 3, HasCompactSupport (χ (n+1) : Space → ℂ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n ≤ 3, ∀ q : Space, ∀ r : ℝ, ∀ hr : 0 < r,
      tsupport (normalizedCutoff L q r hr.ne' (χ (n+1))) ⊆ Metric.closedBall q (c*r) := by
  classical
  choose c hcpos hcs using fun n : Fin 4 => normalizedCutoff_bounded_radius L (χ (n.val+1)) (hc n.val (by omega))
  have hn : 0 ≤ ∑ n : Fin 4, c n := Finset.sum_nonneg (fun n _ => (hcpos n).le)
  refine ⟨1+∑ n : Fin 4, c n,by linarith,?_⟩
  intro n hn q r hr
  apply (hcs ⟨n,by omega⟩ q r hr).trans
  apply Metric.closedBall_subset_closedBall
  apply mul_le_mul_of_nonneg_right _ hr.le
  exact (Finset.single_le_sum (fun i _ => (hcpos i).le) (Finset.mem_univ _)).trans
    (le_add_of_nonneg_left (by norm_num))

lemma closedBall_ball_disjoint_of_radii {b y : Space} {R r : ℝ}
    (hsep : R+r ≤ dist b y) : Disjoint (Metric.closedBall y r) (Metric.ball b R) := by
  rw [Set.disjoint_left]
  intro z hz hzb
  have hzy : dist z y ≤ r := hz
  have hzb' : dist b z < R := by simpa only [dist_comm,Metric.mem_ball] using hzb
  have htri := dist_triangle b z y
  linarith
end GeometricHilbert
end TamingCompatibility

end

end OAI
