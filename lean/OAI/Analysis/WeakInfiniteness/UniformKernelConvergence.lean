import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology

namespace WeakPureInfiniteness

lemma isClosed_setOf_tendsto_zero_of_bound {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (l : Filter ι) (T : ι → E →ₗ[ℂ] F)
    (hT : ∀ᶠ i in l, ∀ x, ‖T i x‖ ≤ ‖x‖) :
    IsClosed {x : E | Tendsto (fun i => T i x) l (𝓝 0)} := by
  apply isClosed_of_closure_subset
  intro x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y,hy,hxy⟩ := Metric.mem_closure_iff.mp hx (ε/2) (by positivity)
  have hy' := (Metric.tendsto_nhds.mp hy) (ε/2) (by positivity)
  filter_upwards [hT,hy'] with i hi hiy
  rw [dist_zero_right] at hiy ⊢
  have hxy' : ‖x-y‖ < ε/2 := by simpa only [dist_eq_norm] using hxy
  have he : T i x = T i (x-y) + T i y := by rw [← map_add,sub_add_cancel]
  rw [he]
  exact (norm_add_le _ _).trans_lt
    ((add_lt_add_of_le_of_lt (hi (x-y)) hiy).trans_le (by linarith))

end WeakPureInfiniteness
end

end OAI
