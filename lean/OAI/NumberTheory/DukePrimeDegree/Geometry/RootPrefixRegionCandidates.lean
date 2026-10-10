import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizedIntersections
import OAI.NumberTheory.DukePrimeDegree.Entropy.RootPrefixLocalConditionals

namespace OAI

/-! # Based remaining-group measures determine kernels on region overlaps -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [SecondCountableTopology T]
    [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hf : c.finalEntries = allPositiveRoots n} {g : G n}

theorem conditional_overlap_of_based_measure
    (B : RootPrefixBox Pfx c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (σ : Measure ((UpperRootTransverse n × T) × c.Time)) [IsFiniteMeasure σ]
    (U : Set ((UpperRootTransverse n × T) × c.Time)) (hU : MeasurableSet U)
    (hres : σ.restrict B.domain = (B.coordinateMeasure μ).restrict U) :
    ∀ᵐ z ∂σ.restrict B.domain,
      ∀ η : Measure (positiveRootGeneratedGroup (allPositiveRoots n \ P)),
        c.remainingGroupLeafMeasure hP hf (B.basedLeaf R μ z) = η →
        let ν := (η.map (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf z.2))).map
          (c.remainingWordHomeomorph hP hf).symm
        let J := (Prod.mk z.1 ⁻¹' U) ∩ B.time
        (anchorNormalize (σ.condKernel z.1) B.time).restrict B.time =
          (anchorNormalize ν J).restrict J := by
  have hac : σ.restrict B.domain ≪ B.coordinateMeasure μ := by
    rw [hres]
    exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have hc := hac.ae_le (B.conditional_of_based_group_measure R hBR μ hfree)
  have hm := hac.ae_le (B.based_group_measure_uncenter_mass R hBR μ hfree)
  have ho := ae_of_ae_map measurable_fst.aemeasurable (B.conditional_on_overlap μ σ U hU hres)
  filter_upwards [hc,hm,ho] with z hcz hmz hoz
  intro η hη
  dsimp only
  refine hoz.2.2.trans ?_
  rw [hcz η hη]
  exact anchorNormalize_restrict_twice _ _ B.time (measurable_prodMk_left hU)
    (hmz η hη).1 (hmz η hη).2

theorem conditional_of_region_time_cover
    (B : RootPrefixBox Pfx c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (σ : Measure ((UpperRootTransverse n × T) × c.Time)) [IsFiniteMeasure σ]
    (U : Set ((UpperRootTransverse n × T) × c.Time)) (hU : MeasurableSet U)
    (hUtime : ∀ z ∈ U, z.2 ∈ B.time) (hsupport : ∀ᵐ z ∂σ, z ∈ U)
    (hres : σ.restrict B.domain = (B.coordinateMeasure μ).restrict U) :
    ∀ᵐ z ∂σ.restrict B.domain,
      ∀ η : Measure (positiveRootGeneratedGroup (allPositiveRoots n \ P)),
        c.remainingGroupLeafMeasure hP hf (B.basedLeaf R μ z) = η →
        let ν := (η.map (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf z.2))).map
          (c.remainingWordHomeomorph hP hf).symm
        (σ.condKernel z.1) =
          (anchorNormalize ν (Prod.mk z.1 ⁻¹' U)).restrict (Prod.mk z.1 ⁻¹' U) := by
  have htime0 : ∀ᵐ z ∂σ, z.2 ∈ B.time := hsupport.mono fun z hz => hUtime z hz
  have H := B.conditional_overlap_of_based_measure R hBR μ hfree σ U hU hres
  have htime : ∀ᵐ s ∂σ.fst, ∀ᵐ t ∂σ.condKernel s, t ∈ B.time := by
    have HT : ∀ᵐ z ∂σ.fst ⊗ₘ σ.condKernel, z.2 ∈ B.time := by
      simpa only [Measure.disintegrate] using htime0
    exact Measure.ae_ae_of_ae_compProd HT
  have ht := ae_of_ae_map measurable_fst.aemeasurable htime
  filter_upwards [H,ae_restrict_of_ae ht] with z hz hzt
  intro η hη
  have hm : σ.condKernel z.1 B.time = 1 := by
    rw [←measure_univ (μ := σ.condKernel z.1)]
    exact measure_congr (ae_eq_univ.mpr hzt)
  have hn : (anchorNormalize (σ.condKernel z.1) B.time).restrict B.time = σ.condKernel z.1 := by
    rw [anchorNormalize,hm,inv_one,one_smul]
    exact Measure.restrict_eq_self_of_ae_mem hzt
  have hJ : (Prod.mk z.1 ⁻¹' U) ∩ B.time = Prod.mk z.1 ⁻¹' U :=
    inter_eq_left.mpr (fun t ht => hUtime (z.1,t) ht)
  simpa only [hn,hJ] using hz η hη


theorem conditional_of_region_contained
    (B : RootPrefixBox Pfx c hP hf g) (R : ℝ) (hBR : B.time ⊆ c.remainingWindow R 0)
    (μ : Measure (X n)) [IsFiniteMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ v ∈ positiveRootGeneratedGroup (allPositiveRoots n),
      rightAction x v = x → v = 1)
    (σ : Measure ((UpperRootTransverse n × T) × c.Time)) [IsFiniteMeasure σ]
    (U : Set ((UpperRootTransverse n × T) × c.Time)) (hU : MeasurableSet U)
    (hUB : U ⊆ B.domain) (hsupport : ∀ᵐ z ∂σ, z ∈ U)
    (hres : σ.restrict B.domain = (B.coordinateMeasure μ).restrict U) :
    ∀ᵐ z ∂σ,
      ∀ η : Measure (positiveRootGeneratedGroup (allPositiveRoots n \ P)),
        c.remainingGroupLeafMeasure hP hf (B.basedLeaf R μ z) = η →
        let ν := (η.map (Homeomorph.mulLeft (c.remainingWordHomeomorph hP hf z.2))).map
          (c.remainingWordHomeomorph hP hf).symm
        (σ.condKernel z.1) =
          (anchorNormalize ν (Prod.mk z.1 ⁻¹' U)).restrict (Prod.mk z.1 ⁻¹' U) := by
  have H := B.conditional_of_region_time_cover R hBR μ hfree σ U hU
    (fun _ hz => (hUB hz).2) hsupport hres
  rwa [Measure.restrict_eq_self_of_ae_mem (hsupport.mono fun _ hz => hUB hz)] at H

end RootPrefixBox
end DukePrimeDegree

end

end OAI
