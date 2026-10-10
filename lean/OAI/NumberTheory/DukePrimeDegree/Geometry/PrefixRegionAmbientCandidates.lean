import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixRegionCandidates
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixAmbientGood

namespace OAI

/-! # One ambient good set for all long-box candidates in a bounded region -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries = allPositiveRoots n) (g : G n)

theorem ae_ambient_region_candidates
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (σ : Measure ((UpperRootTransverse n × T) × c.Time)) [IsFiniteMeasure σ]
    (U : Set ((UpperRootTransverse n × T) × c.Time)) (hU : IsOpen U)
    (he : Topology.IsOpenEmbedding (U.domRestrict (C.timeParam c hP hf g)))
    (hsupport : ∀ᵐ z ∂σ, z ∈ U)
    (hmap : σ.map (C.timeParam c hP hf g) = μ.restrict (C.timeParam c hP hf g '' U))
    (m : ℕ) (htime : ∀ z ∈ U, z.2 ∈ c.remainingWindow 1 m) :
    ∀ᵐ x ∂μ, ∀ B ∈ C.longBoxFamily c hP hf g 1 m,
      ∀ z ∈ B.domain, C.timeParam c hP hf g z = x → z ∈ U →
        ∀ η : Measure (positiveRootGeneratedGroup (allPositiveRoots n \ P)),
          c.remainingGroupLeafMeasure hP hf (B.basedLeaf (1+m) μ z) = η →
          let ν := (η.map (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf z.2))).map
            (c.remainingWordHomeomorph hP hf).symm
          σ.condKernel z.1 =
            (anchorNormalize ν (Prod.mk z.1 ⁻¹' U)).restrict (Prod.mk z.1 ⁻¹' U) := by
  let Q := fun (B : RootPrefixBox C c hP hf g) (z : (UpperRootTransverse n × T) × c.Time) =>
    z ∈ U → ∀ η : Measure (positiveRootGeneratedGroup (allPositiveRoots n \ P)),
      c.remainingGroupLeafMeasure hP hf (B.basedLeaf (1+m) μ z) = η →
      let ν := (η.map (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf z.2))).map
        (c.remainingWordHomeomorph hP hf).symm
      σ.condKernel z.1 =
        (anchorNormalize ν (Prod.mk z.1 ⁻¹' U)).restrict (Prod.mk z.1 ⁻¹' U)
  apply RootPrefixBox.ae_ambient_forall_family (C.longBoxFamily c hP hf g 1 m)
    (C.longBoxFamily_countable c hP hf g 1 m) μ Q
  intro B hB
  have hBt : B.time = c.remainingWindow 1 m := C.longBoxFamily_time c hP hf g 1 m B hB
  have hBR : B.time ⊆ c.remainingWindow (1+m) 0 := by
    rw [hBt]
    simp only [EliminationChain.remainingWindow,Nat.cast_zero,add_zero,subset_refl]
  have hUtime : ∀ z ∈ U, z.2 ∈ B.time := by
    simpa only [hBt] using htime
  have hres := B.restrict_box_eq_coordinateMeasure_restrict U hU he μ σ hsupport hmap
  have H := B.conditional_of_region_time_cover (1+m) hBR μ hfree σ U hU.measurableSet
    hUtime hsupport hres
  rw [hres] at H
  exact (ae_restrict_iff' hU.measurableSet).mp H

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
