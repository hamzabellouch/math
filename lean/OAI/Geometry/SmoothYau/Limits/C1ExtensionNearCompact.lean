import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
namespace YauCounterexamples
open Set Filter MeasureTheory Manifold Function
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma C1_extension_near_compact {K O : Set E} (hK : IsCompact K) (hO : IsOpen O)
    (hKO : K ⊆ O) {φ : E → F} (hφ : ContDiffOn ℝ 1 φ O) :
    ∃ ψ : E → F, ContDiff ℝ 1 ψ ∧ φ =ᶠ[𝓝ˢ K] ψ := by
  obtain ⟨V, hV, hKV, hVO⟩ := normal_exists_closure_subset hK.isClosed hO hKO
  obtain ⟨η, hηone, hηzero, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, E)) (n := 1) (t := V)
      hK.isClosed (by simpa only [hV.interior_eq] using hKV)
  have hη : ContDiff ℝ 1 η := contMDiff_iff_contDiff.mp η.contMDiff
  have hsη : tsupport η ⊆ O := by
    apply (closure_mono (show support η ⊆ V from ?_)).trans hVO
    intro x hx
    by_contra hn
    exact hx (hηzero x hn)
  refine ⟨fun x => η x • φ x, ?_, ?_⟩
  · rw [← contMDiff_iff_contDiff]
    apply contMDiff_of_tsupport
    intro x hx
    have hxO : x ∈ O := hsη (tsupport_smul_subset_left η φ hx)
    rw [contMDiffAt_iff_contDiffAt]
    exact hη.contDiffAt.smul ((hφ x hxO).contDiffAt (hO.mem_nhds hxO))
  · filter_upwards [hηone] with x hx
    simp only [hx, one_smul]
end YauCounterexamples

end

end OAI
