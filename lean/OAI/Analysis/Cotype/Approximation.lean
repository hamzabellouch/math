import OAI.Analysis.Cotype.Target
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
namespace Cotype
variable {X G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem compactMap_approximation (hAP : ApproximationProperty X)
    (J : G →L[ℝ] X) (hJ : IsCompactOperator J) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : X →L[ℝ] X,
      FiniteDimensional ℝ (LinearMap.range S.toLinearMap) ∧ ‖S.comp J - J‖ < δ := by
  have hK : IsCompact (closure (J '' Metric.closedBall 0 1)) :=
    hJ.isCompact_closure_image_closedBall (f := J.toLinearMap) 1
  obtain ⟨S, hS, herr⟩ := hAP _ hK (δ / 2) (by positivity)
  refine ⟨S, hS, lt_of_le_of_lt ?_ (by linarith : δ / 2 < δ)⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro z hz
  have hzK : J z ∈ closure (J '' Metric.closedBall 0 1) :=
    subset_closure ⟨z, by simp [Metric.mem_closedBall, dist_zero_right, hz], rfl⟩
  simpa using (herr (J z) hzK).le

theorem compactMap_finiteRank_approximation (hAP : ApproximationProperty X)
    (J : G →L[ℝ] X) (hJ : IsCompactOperator J) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : G →L[ℝ] X,
      FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧ ‖T - J‖ < δ := by
  obtain ⟨S, hS, herr⟩ := compactMap_approximation hAP J hJ hδ
  let := hS
  refine ⟨S.comp J, ?_, herr⟩
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range S.toLinearMap)
  exact LinearMap.range_comp_le_range _ _

end Cotype

end

end OAI
