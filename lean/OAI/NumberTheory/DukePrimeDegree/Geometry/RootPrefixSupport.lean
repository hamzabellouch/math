import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixRestrictions

namespace OAI

/-! # Supports of actual remaining-root conditional kernels -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hfinal : c.finalEntries = allPositiveRoots n} {g : G n}

lemma coordinateMeasure_ae_domain (B : RootPrefixBox Pfx c hP hfinal g) (μ : Measure (X n)) :
    ∀ᵐ z ∂B.coordinateMeasure μ, z ∈ B.domain := by
  rw [coordinateMeasure]
  exact (ae_map_iff measurable_subtype_coe.aemeasurable
    (B.transverse_open.prod B.time_open).measurableSet).mpr
      (ae_of_all _ fun z => z.prop)

lemma coordinateMeasure_fst_ae_transverse (B : RootPrefixBox Pfx c hP hfinal g) (μ : Measure (X n)) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, s ∈ B.transverse := by
  rw [Measure.fst]
  apply (ae_map_iff measurable_fst.aemeasurable B.transverse_open.measurableSet).mpr
  filter_upwards [B.coordinateMeasure_ae_domain μ] with z hz
  exact hz.1

lemma conditionalKernel_ae_time (B : RootPrefixBox Pfx c hP hfinal g) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, ∀ᵐ t ∂B.conditionalKernel μ s, t ∈ B.time := by
  have H : ∀ᵐ z ∂((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ), z.2 ∈ B.time := by
    rw [conditionalKernel, Measure.disintegrate]
    filter_upwards [B.coordinateMeasure_ae_domain μ] with z hz
    exact hz.2
  exact Measure.ae_ae_of_ae_compProd H

lemma conditionalKernel_time_mass (B : RootPrefixBox Pfx c hP hfinal g) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, B.conditionalKernel μ s B.time = 1 := by
  filter_upwards [B.conditionalKernel_ae_time μ] with s hs
  rw [← measure_univ (μ := B.conditionalKernel μ s)]
  exact measure_congr (ae_eq_univ.mpr hs)


end RootPrefixBox
end DukePrimeDegree

end

end OAI
