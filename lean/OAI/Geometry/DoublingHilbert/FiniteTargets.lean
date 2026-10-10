import Mathlib

namespace OAI

open Set Metric
open scoped BigOperators
open Filter
open scoped Topology
noncomputable section
namespace CompactBanach

theorem euclidean_embedding_of_finite_dimensional
    {X E : Type*} [MetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : X → E) {a D : ℝ} (ha : 0 < a) (hD : 1 ≤ D)
    (hf : ∀ x y, a * dist x y ≤ dist (f x) (f y) ∧
      dist (f x) (f y) ≤ D * a * dist x y) :
    ∃ g : X → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
      ∃ b : ℝ, 0 < b ∧ ∃ A : ℝ, 1 ≤ A ∧ ∀ x y,
        b * dist x y ≤ dist (g x) (g y) ∧
          dist (g x) (g y) ≤ A * b * dist x y := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let U : ℝ := ‖e.toContinuousLinearMap‖ + 1
  let V : ℝ := ‖e.symm.toContinuousLinearMap‖ + 1
  have hU : 1 ≤ U := le_add_of_nonneg_left (norm_nonneg _)
  have hV : 1 ≤ V := le_add_of_nonneg_left (norm_nonneg _)
  have hVp : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hUp : 0 < U := lt_of_lt_of_le zero_lt_one hU
  have hu (x y : E) : dist (e x) (e y) ≤ U * dist x y := by
    have h := e.toContinuousLinearMap.lipschitzWith.dist_le_mul x y
    calc
      _ ≤ ‖e.toContinuousLinearMap‖ * dist x y := h
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [U]; linarith) dist_nonneg
  have hl (x y : E) : dist x y ≤ V * dist (e x) (e y) := by
    have h := e.symm.toContinuousLinearMap.lipschitzWith.dist_le_mul (e x) (e y)
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h
    calc
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * dist (e x) (e y) := h
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [V]; linarith) dist_nonneg
  have hDU : 1 ≤ D * U := by nlinarith
  have hA : 1 ≤ D * U * V := by nlinarith
  refine ⟨e ∘ f, a / V, div_pos ha hVp, D * U * V, hA, ?_⟩
  intro x y
  dsimp only [Function.comp_apply]
  constructor
  · have hh := (hf x y).1.trans (hl (f x) (f y))
    calc
      _ = (a * dist x y) / V := by ring
      _ ≤ _ := (div_le_iff₀ hVp).mpr (by nlinarith only [hh])
  · calc
      _ ≤ U * dist (f x) (f y) := hu _ _
      _ ≤ U * (D * a * dist x y) := mul_le_mul_of_nonneg_left (hf x y).2 hUp.le
      _ = (D * U * V) * (a / V) * dist x y := by field_simp

end CompactBanach
end

end OAI
