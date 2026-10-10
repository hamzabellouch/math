import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped ContDiff Topology
open Set
open Set Filter
open scoped Topology ContDiff Manifold
namespace YauCounterexamples

lemma exists_smooth_complex_cutoff (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ ζ : (Fin 3 → ℝ) → ℂ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ Metric.ball 0 ρ ∧ ζ =ᶠ[𝓝 0] (fun _ => 1) := by
  have hsub : ({(0 : Fin 3 → ℝ)} : Set (Fin 3 → ℝ)) ⊆
      interior (Metric.closedBall 0 (ρ/2)) := by
    rw [interior_closedBall _ (ne_of_gt (half_pos hρ))]
    exact singleton_subset_iff.mpr (Metric.mem_ball_self (half_pos hρ))
  obtain ⟨f,hf1,hf0,hfI⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ,Fin 3 → ℝ)) (n := ⊤) isClosed_singleton hsub
  let ζ : (Fin 3 → ℝ) → ℂ := fun x => (f x : ℂ)
  have hs : tsupport ζ ⊆ Metric.closedBall 0 (ρ/2) := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    by_contra h
    exact hx (by simp [ζ,hf0 x h])
  refine ⟨ζ,Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.mp f.contMDiff),
    (isCompact_closedBall 0 (ρ/2)).of_isClosed_subset isClosed_closure hs,
    hs.trans (Metric.closedBall_subset_ball (half_lt_self hρ)),?_⟩
  have hh : ∀ᶠ x in 𝓝 (0 : Fin 3 → ℝ), f x = 1 := by simpa using hf1
  filter_upwards [hh] with x hx
  simp [ζ,hx]

end YauCounterexamples
end

end OAI
