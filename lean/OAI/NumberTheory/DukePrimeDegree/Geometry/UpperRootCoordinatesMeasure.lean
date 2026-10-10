import OAI.NumberTheory.DukePrimeDegree.Geometry.UpperRootDisintegration

namespace OAI

/-!
# Support and ambient null sets in upper-root coordinate measures
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set

namespace DukePrimeDegree
open PrimeDegreePackets

namespace UpperRootBox
variable {n : ℕ} {g : G n}

lemma coordinateMeasure_ae_domain (B : UpperRootBox n g) (μ : Measure (X n)) :
    ∀ᵐ z ∂B.coordinateMeasure μ, z ∈ B.domain := by
  rw [coordinateMeasure]
  exact (ae_map_iff measurable_subtype_coe.aemeasurable
    (B.transverse_open.prod B.time_open).measurableSet).mpr
      (ae_of_all _ fun z => z.prop)

lemma coordinateMeasure_fst_ae_transverse (B : UpperRootBox n g) (μ : Measure (X n)) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, s ∈ B.transverse := by
  rw [Measure.fst]
  apply (ae_map_iff measurable_fst.aemeasurable B.transverse_open.measurableSet).mpr
  filter_upwards [B.coordinateMeasure_ae_domain μ] with z hz
  exact hz.1

lemma conditionalKernel_ae_time (B : UpperRootBox n g) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, ∀ᵐ t ∂B.conditionalKernel μ s, t ∈ B.time := by
  have H : ∀ᵐ z ∂((B.coordinateMeasure μ).fst ⊗ₘ B.conditionalKernel μ), z.2 ∈ B.time := by
    rw [conditionalKernel, Measure.disintegrate]
    filter_upwards [B.coordinateMeasure_ae_domain μ] with z hz
    exact hz.2
  exact Measure.ae_ae_of_ae_compProd H

lemma conditionalKernel_time_mass (B : UpperRootBox n g) (μ : Measure (X n))
    [IsFiniteMeasure μ] :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst, B.conditionalKernel μ s B.time = 1 := by
  filter_upwards [B.conditionalKernel_ae_time μ] with s hs
  rw [← measure_univ (μ := B.conditionalKernel μ s)]
  exact measure_congr (ae_eq_univ.mpr hs)

lemma ae_coordinate_of_ambient (B : UpperRootBox n g) (μ : Measure (X n))
    {P : X n → Prop} (hp : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ z ∂B.coordinateMeasure μ, P (upperRootQuotientParam n g z) := by
  have H : ∀ᵐ x ∂μ.restrict B.range, P x := ae_restrict_of_ae hp
  rw [← B.map_coordinateMeasure μ] at H
  exact ae_of_ae_map (upperRootQuotientParam_localHomeomorph n g).continuous.measurable.aemeasurable H

end UpperRootBox
end DukePrimeDegree

end

end OAI
