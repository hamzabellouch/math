import OAI.NumberTheory.DukePrimeDegree.Geometry.PrefixRegionAmbientCandidates
import OAI.NumberTheory.DukePrimeDegree.Geometry.RemainingIntrinsicProduct

namespace OAI

/-! # From intrinsic long-box leaves to an actual regional conditional kernel -/

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

omit [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] in
theorem timeParam_injective_of_free_at_coordinate
    (z : (UpperRootTransverse n × T) × c.Time)
    (hfree : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction (C.timeParam c hP hf g z) v = C.timeParam c hP hf g z → v = 1) :
    Function.Injective (fun t => C.timeParam c hP hf g (z.1,t)) := by
  apply C.timeParam_injective_of_free c hP hf g z.1
  apply subgroup_free_of_free_translate (positiveRootGeneratedGroup (allPositiveRoots n))
    (Quotient.mk _ ((g*z.1.1.val)*C.base z.1.2)) (c.word z.2)
    (positiveRootGeneratedGroup_mono Finset.sdiff_subset (c.word_mem_remaining hf z.2))
  simpa only [C.timeParam_eq_action] using hfree

theorem ae_region_kernel_of_intrinsic_boxes
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (σ : Measure ((UpperRootTransverse n × T) × c.Time)) [IsFiniteMeasure σ]
    (U : Set ((UpperRootTransverse n × T) × c.Time)) (hU : IsOpen U)
    (he : Topology.IsOpenEmbedding (U.domRestrict (C.timeParam c hP hf g)))
    (hsupport : ∀ᵐ z ∂σ, z ∈ U)
    (hmap : σ.map (C.timeParam c hP hf g) = μ.restrict (C.timeParam c hP hf g '' U))
    (m : ℕ) (htime : ∀ z ∈ U, z.2 ∈ c.remainingWindow 1 m)
    (hIH : ∀ B ∈ C.longBoxFamily c hP hf g 1 m,
      ∀ᵐ z ∂B.coordinateMeasure μ,
        c.remainingGroupLeafMeasure hP hf (B.basedLeaf (1+m) μ z) =
          c.remainingIntrinsicProduct hP hf μ (C.timeParam c hP hf g z)) :
    ∀ᵐ x ∂μ, ∀ z ∈ U, C.timeParam c hP hf g z = x →
      σ.condKernel z.1 =
        (anchorNormalize
          (((c.remainingIntrinsicProduct hP hf μ x).map
            (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf z.2))).map
              (c.remainingWordHomeomorph hP hf).symm)
          (Prod.mk z.1 ⁻¹' U)).restrict (Prod.mk z.1 ⁻¹' U) := by
  have HC := C.ae_ambient_region_candidates c hP hf g μ hfree σ U hU he hsupport hmap m htime
  have HI := RootPrefixBox.ae_ambient_forall_family (C.longBoxFamily c hP hf g 1 m)
    (C.longBoxFamily_countable c hP hf g 1 m) μ
    (fun B z => c.remainingGroupLeafMeasure hP hf (B.basedLeaf (1+m) μ z) =
      c.remainingIntrinsicProduct hP hf μ (C.timeParam c hP hf g z)) hIH
  filter_upwards [HC,HI,hfree] with x hc hi hx
  intro z hz hzx
  have hfz : ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction (C.timeParam c hP hf g z) v = C.timeParam c hP hf g z → v = 1 := by
    simpa only [hzx] using hx
  obtain ⟨B,hB,hzB⟩ := C.longBoxFamily_covers c hP hf g 1 m z.1
    (C.timeParam_injective_of_free_at_coordinate c hP hf g z hfz)
  have hzD : z ∈ B.domain := by
    refine ⟨hzB,?_⟩
    rw [C.longBoxFamily_time c hP hf g 1 m B hB]
    exact htime z hz
  apply hc B hB z hzD hzx hz (c.remainingIntrinsicProduct hP hf μ x)
  simpa only [hzx] using hi B hB z hzD hzx

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
