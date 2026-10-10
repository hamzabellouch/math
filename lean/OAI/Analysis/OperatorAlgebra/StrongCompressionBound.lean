import Mathlib

namespace OAI

/-! Recovering an operator norm bound from finite-corner bounds in a
strongly exhausting family of compressions. -/

noncomputable section
open Filter Topology

namespace WeakPureInfiniteness

variable {ι H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Uniformly contractive compressions converging strongly to the identity
recover every operator strongly, including on its moving input vector. -/
lemma strong_compressions_tendsto (l : Filter ι) (P : ι → H →L[ℂ] H)
    (hPn : ∀ i, ‖P i‖ ≤ 1) (hP : ∀ x, Tendsto (fun i => P i x) l (𝓝 x))
    (T : H →L[ℂ] H) (x : H) :
    Tendsto (fun i => (P i * T * P i) x) l (𝓝 (T x)) := by
  have ht : Tendsto (fun i => T (P i x) - T x) l (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self] using (T.continuous.continuousAt.tendsto.comp (hP x)).sub
      (tendsto_const_nhds : Tendsto (fun _ : ι => T x) l (𝓝 (T x)))
  have htn : Tendsto (fun i => ‖T (P i x) - T x‖) l (𝓝 0) := by
    simpa only [norm_zero] using ht.norm
  have he : Tendsto (fun i => P i (T (P i x) - T x)) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => (P i).le_opNorm _ |>.trans ?_) htn
    exact (mul_le_mul_of_nonneg_right (hPn i) (norm_nonneg _)).trans_eq (one_mul _)
  have hh := he.add (hP (T x))
  simpa only [map_sub, sub_add_cancel, zero_add, mul_apply_eq_comp] using hh

/-- A bound on every strongly exhausting compression is a bound on the
original operator. No norm convergence of the projections is needed. -/
theorem norm_le_of_strong_compression_bound (l : Filter ι) [NeBot l]
    (P : ι → H →L[ℂ] H) (hPn : ∀ i, ‖P i‖ ≤ 1)
    (hP : ∀ x, Tendsto (fun i => P i x) l (𝓝 x))
    (T : H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ i, ‖P i * T * P i‖ ≤ C) : ‖T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound T hC
  intro x
  apply le_of_tendsto (strong_compressions_tendsto l P hPn hP T x).norm
  exact Eventually.of_forall fun i => ((P i * T * P i).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg x))

end WeakPureInfiniteness

end

end OAI
