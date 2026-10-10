import Mathlib

namespace OAI

noncomputable section

namespace KKTraceTransfer

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem bounded_evals_continuous {X : Type*} [TopologicalSpace X]
    (F : X → (H →L[ℂ] H)) (hF : ∀ a, ‖F a‖ ≤ 1)
    (D : ℕ → H) (hD : DenseRange D) (hc : ∀ j, Continuous (fun a => F a (D j)))
    (ξ : H) : Continuous (fun a => F a ξ) := by
  have hLip (a : X) (x y : H) : dist (F a x) (F a y) ≤ dist x y := by
    rw [dist_eq_norm,dist_eq_norm,←map_sub]
    exact ((F a).le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right (hF a) (norm_nonneg (x-y)))
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := hD.exists_dist_lt ξ (show 0 < ε/4 by positivity)
  have hjc := Metric.tendsto_nhds.mp ( (hc j).continuousAt (x := a)) (ε/2) (show 0 < ε/2 by positivity)
  filter_upwards [hjc] with b hb
  calc
    dist (F b ξ) (F a ξ) ≤ dist (F b ξ) (F b (D j)) +
        (dist (F b (D j)) (F a (D j)) + dist (F a (D j)) (F a ξ)) :=
      (dist_triangle (F b ξ) (F b (D j)) (F a ξ)).trans
        (add_le_add (le_refl _) (dist_triangle (F b (D j)) (F a (D j)) (F a ξ)))
    _ ≤ dist ξ (D j) + (dist (F b (D j)) (F a (D j)) + dist (D j) ξ) :=
      add_le_add (hLip b _ _) (add_le_add (le_refl _) (hLip a _ _))
    _ < ε := by rw [dist_comm (D j) ξ]; linarith

end

end KKTraceTransfer
end

end OAI
