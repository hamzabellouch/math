import Mathlib

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter
namespace YauCounterexamples
lemma compact_strict_profile_ratio {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {r φ : X → ℝ}
    (hr : ContinuousOn r K) (hφ : ContinuousOn φ K)
    (hr0 : ∀ y ∈ K, 0 ≤ r y)
    (hgap : ∀ y ∈ K, r y ≠ 0 → Real.log (r y) < φ y) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ y ∈ K, r y ≤ ρ*Real.exp (φ y) := by
  classical
  by_cases hne : K.Nonempty
  · let f := fun y => r y / Real.exp (φ y)
    have hf : ContinuousOn f K := hr.div hφ.rexp (fun y _ => (Real.exp_pos _).ne')
    obtain ⟨z,hz,hm⟩ := hK.exists_isMaxOn hne hf
    have hlt : f z < 1 := by
      dsimp [f]
      apply (div_lt_one (Real.exp_pos _)).mpr
      by_cases hz0 : r z=0
      · rw [hz0]; exact Real.exp_pos _
      · have hrpos : 0 < r z := lt_of_le_of_ne (hr0 z hz) (Ne.symm hz0)
        rw [←Real.exp_log hrpos]
        exact Real.exp_lt_exp.mpr (hgap z hz hz0)
    have hnonneg : 0 ≤ f z := div_nonneg (hr0 z hz) (Real.exp_pos _).le
    refine ⟨(f z+1)/2,by linarith,by linarith,?_⟩
    intro y hy
    apply (div_le_iff₀ (Real.exp_pos (φ y))).mp
    have hh : f y ≤ f z := hm hy
    change f y ≤ _
    linarith
  · refine ⟨1/2,by norm_num,by norm_num,?_⟩
    intro y hy
    exact (hne ⟨y,hy⟩).elim

end YauCounterexamples

end

end OAI
