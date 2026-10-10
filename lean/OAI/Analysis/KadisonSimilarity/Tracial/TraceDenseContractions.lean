import OAI.Analysis.KadisonSimilarity.Tracial.PredualGNSSeparable
import OAI.Analysis.KadisonSimilarity.Tracial.TracialMomentContinuity

namespace OAI

/-! A countable family of contractions dense for the trace norm. -/

noncomputable section
namespace KadisonSimilarity
open BoundedHochschild Generator.Tracial Filter Topology
open scoped ComplexOrder

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  (τ : B →ₚ[ℂ] ℂ)

/-- Separability of the GNS space suffices; the algebra need not be norm separable. -/
theorem exists_trace_dense_contractions [TopologicalSpace.SeparableSpace τ.GNS] :
    ∃ d : ℕ → B, (∀ n, ‖d n‖ ≤ 1) ∧
      ∀ b : B, ‖b‖ ≤ 1 → ∃ j : ℕ → ℕ,
        GNSTendsto τ (fun k => d (j k)) atTop b := by
  classical
  let S : Set τ.GNS := gnsTracialVector τ '' Metric.closedBall (0 : B) 1
  let : Nonempty S := ⟨⟨gnsTracialVector τ 0, ⟨0, by simp, rfl⟩⟩⟩
  let z : ℕ → S := TopologicalSpace.denseSeq S
  choose d hd he using fun n => (z n).property
  refine ⟨d, fun n => by simpa only [Metric.mem_closedBall, dist_zero_right] using hd n, ?_⟩
  intro b hb
  let x : S := ⟨gnsTracialVector τ b, ⟨b, by simpa using hb, rfl⟩⟩
  obtain ⟨y, hy, hyt⟩ := mem_closure_iff_seq_limit.mp
    ((TopologicalSpace.denseRange_denseSeq S) x)
  choose j hj using hy
  have hc : Tendsto (fun k => gnsTracialVector τ (d (j k))) atTop
      (𝓝 (gnsTracialVector τ b)) := by
    have ht := continuous_subtype_val.tendsto x |>.comp hyt
    have hf : (fun k => gnsTracialVector τ (d (j k))) = fun k => (y k : τ.GNS) := by
      funext k
      exact (he (j k)).trans (congrArg Subtype.val (hj k))
    rw [hf]
    exact ht
  refine ⟨j, ?_⟩
  have ht := (hc.sub_const (gnsTracialVector τ b)).norm
  have hn (k : ℕ) : ‖gnsTracialVector τ (d (j k)) - gnsTracialVector τ b‖ =
      ‖τ.toPreGNS (d (j k) - b)‖ := by
    rw [← map_sub, gnsTracialVector_apply, UniformSpace.Completion.norm_coe]
  simpa only [GNSTendsto, hn, sub_self, norm_zero] using ht

end KadisonSimilarity

end

end OAI
