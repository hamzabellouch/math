import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSimpleKernelEstimate

namespace OAI

/-! Bounded solutions of compact equations converge when their forcing does.
This also applies to divided differences of normalized pencil eigenvectors. -/

open Set Filter Topology
namespace DefocusingNLS

theorem compact_forced_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) (v : ℕ → E)
    (M : ℝ) (hM : ∀ n, ‖v n‖ ≤ M) (f : E)
    (hf : Tendsto (fun n => v n - K (v n)) atTop (𝓝 f)) :
    ∃ v₀ : E, v₀ - K v₀ = f ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun n => v (φ n)) atTop (𝓝 v₀) := by
  have hb (n : ℕ) : v n ∈ Metric.closedBall (0 : E) M := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hM n
  have hcomp := hK.isCompact_closure_image_closedBall M
  obtain ⟨w₀, _, φ, hφ, ht⟩ := hcomp.tendsto_subseq
    (fun n => subset_closure (mem_image_of_mem K (hb n)))
  have hv : Tendsto (fun n => v (φ n)) atTop (𝓝 (f + w₀)) := by
    have hh := (hf.comp hφ.tendsto_atTop).add ht
    simpa only [Function.comp_def, sub_add_cancel] using hh
  have he : (f + w₀) - K (f + w₀) = f :=
    tendsto_nhds_unique (hv.sub (K.continuous.continuousAt.tendsto.comp hv))
      (hf.comp hφ.tendsto_atTop)
  exact ⟨f + w₀, he, φ, hφ, hv⟩

end DefocusingNLS

end OAI
