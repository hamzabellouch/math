import OAI.GroupTheory.PolycyclicRecognition.Analysis.AsymptoticEquicontinuity
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

/-! # Compact containment for families of chart profiles -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {X W I : Type*} [TopologicalSpace X] [MetricSpace W] [ProperSpace W]

/-- Equicontinuous profiles with pointwise bounded values lie in one compact
set for locally uniform convergence. The domain need not itself be compact. -/
theorem exists_compact_containing_profiles
    (F : I → C(X, W)) (hequi : Equicontinuous (fun i x => F i x))
    (w₀ : W) (hbound : ∀ x, ∃ R : ℝ, ∀ i, dist (F i x) w₀ ≤ R) :
    ∃ S : Set C(X, W), IsCompact S ∧ ∀ i, F i ∈ S := by
  let A : Set (X → W) := range (fun i x => F i x)
  have hA : A.Equicontinuous := by
    exact (equicontinuous_iff_range).mp hequi
  have hcls : (closure A).Equicontinuous := hA.closure
  have hcontinuous : ∀ f ∈ closure A, Continuous f := by
    intro f hf
    exact hcls.continuous ⟨f, hf⟩
  choose R hR using hbound
  have hsubset : A ⊆ {f : X → W | ∀ x, f x ∈ closedBall w₀ (R x)} := by
    rintro f ⟨i, rfl⟩ x
    exact hR x i
  have hclosed : IsClosed {f : X → W | ∀ x, f x ∈ closedBall w₀ (R x)} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_closedBall.preimage (continuous_apply x))
  have hcompact : IsCompact (closure A) :=
    (isCompact_pi_infinite (fun x => isCompact_closedBall w₀ (R x))).of_isClosed_subset
      isClosed_closure (closure_minimal hsubset hclosed)
  let S : Set C(X, W) := {f | (f : X → W) ∈ closure A}
  have himage : ContinuousMap.toFun '' S = closure A := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f, hcontinuous f hf⟩, hf, rfl⟩
  refine ⟨S, ?_, ?_⟩
  · apply ArzelaAscoli.isCompact_of_equicontinuous S
    · rwa [himage]
    · exact hcls.comp (fun f : S => ⟨f.val, f.property⟩)
  · intro i
    exact subset_closure (mem_range_self i)

end PolycyclicRecognition

end

end OAI
