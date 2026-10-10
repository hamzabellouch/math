import OAI.Analysis.IrrationalRotation.Model.RealTriangularLaw
import OAI.Analysis.IrrationalRotation.Couplings.ProductCouplingCircle
import OAI.Analysis.IrrationalRotation.Sampling.ProductSampling

namespace OAI

noncomputable section
open MeasureTheory Set Filter

namespace Invariant233.OrderedProductCoupling

lemma circlePairEndpoint_measurable : Measurable circlePairEndpoint :=
  circleEndpoint_measurable.prodMap circleEndpoint_measurable

lemma measurePreserving_circlePairEndpoint :
    MeasurePreserving circlePairEndpoint (baseMeasure.prod baseMeasure)
      (ProductModel.baseMeasure.prod ProductModel.baseMeasure) :=
  measurePreserving_circleEndpoint.prod measurePreserving_circleEndpoint

lemma realSelectedEndpoint_measurable (I : Finset ℕ) :
    Measurable (fun xz : Endpoint × Endpoint => realSelectedEndpoint I xz.1 xz.2) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i ∈ I
  · simpa [realSelectedEndpoint, hi, Function.comp_def] using
      (measurable_pi_apply i).comp measurable_snd
  · simpa [realSelectedEndpoint, hi, Function.comp_def] using
      (measurable_pi_apply i).comp measurable_fst

lemma circleEndpoint_realSelectedEndpoint (I : Finset ℕ) (x z : Endpoint) :
    circleEndpoint (realSelectedEndpoint I x z) =
      ProductModel.selectedEndpoint I (circleEndpoint x) (circleEndpoint z) := by
  funext i
  by_cases hi : i ∈ I <;>
    simp [circleEndpoint, realSelectedEndpoint, ProductModel.selectedEndpoint, hi]

lemma realTriangularEvent_ae_preimage (I : Finset ℕ) :
    realTriangularEvent I =ᵐ[baseMeasure.prod baseMeasure]
      circlePairEndpoint ⁻¹' ProductModel.triangularEvent I := by
  have hx : ∀ᵐ xz ∂baseMeasure.prod baseMeasure,
      realEndpoint (circleEndpoint xz.1) = xz.1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae ae_realEndpoint_circleEndpoint
  have hz : ∀ᵐ xz ∂baseMeasure.prod baseMeasure,
      realEndpoint (circleEndpoint xz.2) = xz.2 :=
    measurePreserving_snd.quasiMeasurePreserving.ae ae_realEndpoint_circleEndpoint
  filter_upwards [hx, hz] with xz hx hz
  change (∀ i ∈ I, xz.1 i < xz.2 i) =
    (∀ i ∈ I, realEndpoint (circleEndpoint xz.1) i < realEndpoint (circleEndpoint xz.2) i)
  rw [hx, hz]

lemma map_restrict_realTriangularEvent (I : Finset ℕ) :
    ((baseMeasure.prod baseMeasure).restrict (realTriangularEvent I)).map circlePairEndpoint =
      (ProductModel.baseMeasure.prod ProductModel.baseMeasure).restrict
        (ProductModel.triangularEvent I) := by
  rw [Measure.restrict_congr_set (realTriangularEvent_ae_preimage I),
    ← Measure.restrict_map circlePairEndpoint_measurable
      (ProductModel.Sampling.triangularEvent_measurable I),
    measurePreserving_circlePairEndpoint.map_eq]

theorem map_realTriangularLaw (I : Finset ℕ) :
    (realTriangularLaw I).map circlePairEndpoint = ProductModel.triangularLaw I := by
  have hm := measurable_fst.prodMk (realSelectedEndpoint_measurable I)
  rw [realTriangularLaw, Measure.map_map circlePairEndpoint_measurable hm]
  have hcomp : circlePairEndpoint ∘ (fun xz : Endpoint × Endpoint =>
      (xz.1, realSelectedEndpoint I xz.1 xz.2)) =
      (fun xz : ProductModel.EndpointPair =>
        (xz.1, ProductModel.selectedEndpoint I xz.1 xz.2)) ∘ circlePairEndpoint := by
    funext xz
    exact Prod.ext rfl (circleEndpoint_realSelectedEndpoint I xz.1 xz.2)
  rw [hcomp, ← Measure.map_map (ProductModel.Sampling.endpointMap_measurable I)
    circlePairEndpoint_measurable, map_restrict_realTriangularEvent]
  rfl

theorem map_absolutelyContinuous_triangularLaw (I : Finset ℕ)
    {ν : Measure (Endpoint × Endpoint)} (hν : ν ≪ realTriangularLaw I) :
    ν.map circlePairEndpoint ≪ ProductModel.triangularLaw I := by
  simpa only [map_realTriangularLaw] using hν.map circlePairEndpoint_measurable

end Invariant233.OrderedProductCoupling

end

end OAI
