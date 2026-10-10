import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Function Filter
open scoped Topology Manifold ContDiff
namespace YauCounterexamples
section PatchCutoffs
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_finite_patch_partition (U : M → Set M) (hU : ∀ p, IsOpen (U p))
    (hp : ∀ p, p ∈ U p) :
    ∃ t : Finset M, ∃ ρ : SmoothPartitionOfUnity t 𝓘(ℝ, E) M univ,
      ρ.IsSubordinate (fun i => U (i : M)) := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU
    (by intro x _; exact mem_iUnion_of_mem x (hp x))
  refine ⟨t, ?_⟩
  apply SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, E)) isClosed_univ
    (fun i : t => U (i : M)) (fun i => hU (i : M))
  intro x hx
  obtain ⟨p, hp, hpx⟩ := mem_iUnion₂.mp (ht hx)
  exact mem_iUnion_of_mem ⟨p, hp⟩ hpx

theorem exists_patch_buffer {U : Set M} (hU : IsOpen U) {η : M → ℂ}
    (hs : tsupport η ⊆ U) :
    ∃ χ : M → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ χ ∧
      tsupport χ ⊆ U ∧ χ =ᶠ[𝓝ˢ (tsupport η)] 1 := by
  obtain ⟨v, hv, hηv, hvc⟩ := normal_exists_closure_subset (isClosed_tsupport η) hU hs
  obtain ⟨f, hf1, hf0, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := 𝓘(ℝ, E)) (n := ⊤) (isClosed_tsupport η)
    (t := v) (by simpa only [hv.interior_eq] using hηv)
  refine ⟨fun x => (f x : ℂ), Complex.ofRealCLM.contMDiff.comp f.contMDiff, ?_, ?_⟩
  · apply (closure_mono (show support (fun x => (f x : ℂ)) ⊆ v from ?_)).trans hvc
    intro x hx
    by_contra h
    exact hx (by simp [hf0 x h])
  · filter_upwards [hf1] with x hx
    simp only [hx, Complex.ofReal_one, Pi.one_apply]

end PatchCutoffs
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def unitBump : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩

def complexUnitBump (x : E) : ℂ := (unitBump E x : ℂ)

lemma contDiff_complexUnitBump : ContDiff ℝ ∞ (complexUnitBump E) :=
  Complex.ofRealCLM.contDiff.comp (unitBump E).contDiff

lemma hasCompactSupport_complexUnitBump : HasCompactSupport (complexUnitBump E) := by
  apply (unitBump E).hasCompactSupport.mono
  intro x hx
  exact fun h => hx (by simp [complexUnitBump, h])

lemma complexUnitBump_eq_one {x : E} (hx : ‖x‖ ≤ 1) : complexUnitBump E x = 1 := by
  have hh : x ∈ Metric.closedBall (0 : E) (unitBump E).rIn := by
    simpa only [Metric.mem_closedBall, dist_zero_right, unitBump] using hx
  simp only [complexUnitBump, (unitBump E).one_of_mem_closedBall hh, Complex.ofReal_one]

end YauCounterexamples


end

end OAI
