import OAI.Probability.FreeIsing.Gaussian.TreeResponsePlanted
import OAI.Probability.FreeIsing.Trees.ResponseSourceInvariance

namespace OAI

noncomputable section

namespace Problem367.GaussianTreeResponse

theorem finiteRow_update_source {d : ℕ} (beta : ℝ)
    (E : Finset (TreeVertex d)) (r : E) (h x : TreeVertex d → ℝ)
    (v : TreeVertex d) (y : E → ℝ) (z : ℝ) :
    finiteRow beta E r h x v (Function.update y r z) = finiteRow beta E r h x v y := by
  classical
  by_cases hv : v ∈ E
  · simp only [finiteRow, ite_eq_left hv]
    apply TreePathResponse.response_eq_of_eq_off_source beta r.property
    intro w hw
    by_cases hwe : w ∈ E
    · simp only [Function.updateFinset, dite_eq_left hwe]
      rw [Function.update_of_ne (show (⟨w, hwe⟩ : E) ≠ r from
        fun he => hw (congrArg Subtype.val he))]
    · simp only [Function.updateFinset, dite_eq_right hwe]
  · simp only [finiteRow, ite_eq_right hv]

theorem finiteRow_energy_update_source {d : ℕ} (beta : ℝ)
    (E : Finset (TreeVertex d)) (r : E) (h x : TreeVertex d → ℝ)
    (y : E → ℝ) (z : ℝ) :
    (∑' v, finiteRow beta E r h x v (Function.update y r z) ^ 2) =
      ∑' v, finiteRow beta E r h x v y ^ 2 := by
  exact tsum_congr fun v => by rw [finiteRow_update_source]

theorem observedRow_update_source_noise {d : ℕ} (beta : ℝ)
    (E : Finset (TreeVertex d)) {r : TreeVertex d} (hr : r ∈ E)
    (t : ℝ) (v : TreeVertex d) (σ : TreeVertex d → IsingSpin)
    (y : TreeVertex d → ℝ) (z : ℝ) :
    observedRow beta E r t v (σ, Function.update y r z) =
      observedRow beta E r t v (σ, y) := by
  classical
  by_cases hv : v ∈ E
  · simp only [observedRow, ite_eq_left hv]
    apply TreePathResponse.response_eq_of_eq_off_source beta hr
    intro w hw
    simp only [PlantedSymmetry.observation, Function.update_of_ne hw]
  · simp only [observedRow, ite_eq_right hv]

theorem observedRow_energy_update_source_noise {d : ℕ} (beta : ℝ)
    (E : Finset (TreeVertex d)) {r : TreeVertex d} (hr : r ∈ E)
    (t : ℝ) (σ : TreeVertex d → IsingSpin) (y : TreeVertex d → ℝ) (z : ℝ) :
    (∑' v, observedRow beta E r t v (σ, Function.update y r z) ^ 2) =
      ∑' v, observedRow beta E r t v (σ, y) ^ 2 := by
  exact tsum_congr fun v => by rw [observedRow_update_source_noise beta E hr]

end Problem367.GaussianTreeResponse

end

end OAI
