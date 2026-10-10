import OAI.Analysis.IrrationalRotation.Model.ProductTailDensity
import OAI.Analysis.IrrationalRotation.Couplings.BiasedTailDensity
import OAI.Analysis.IrrationalRotation.Product.ProductCoordinateSplit
import OAI.Analysis.IrrationalRotation.Analysis.DensityTransport

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace Invariant233.ProductModel

instance prefixMeasure_probability (D : ℕ) : IsProbabilityMeasure (prefixMeasure D) := by
  unfold prefixMeasure
  infer_instance

instance tailMeasure_probability (D : ℕ) : IsProbabilityMeasure (tailMeasure D) := by
  unfold tailMeasure
  infer_instance

theorem measurePreserving_splitCoordinates (D : ℕ) :
    MeasurePreserving (splitCoordinates D) baseMeasure
      ((prefixMeasure D).prod (tailMeasure D)) :=
  ProductCoordinateSplit.measurePreserving_split (fun _ : ℕ => circleMeasure) (fun i => i < D)

theorem prefixTailDensity_spec (D : ℕ) {g : Base → ℝ}
    (hg : MemLp g 2 baseMeasure) (hn : 0 ≤ᵐ[baseMeasure] g)
    (hmass : ∫ x, g x ∂baseMeasure = 1) :
    MemLp (prefixTailDensity D g) 2 (tailMeasure D) ∧
      0 ≤ᵐ[tailMeasure D] prefixTailDensity D g ∧
      (∫ z, prefixTailDensity D g z ∂tailMeasure D) = 1 ∧
      eLpNorm (prefixTailDensity D g) 2 (tailMeasure D) ≤ eLpNorm g 2 baseMeasure ∧
      (baseMeasure.withDensity (fun x => ENNReal.ofReal (g x))).map (tailCoordinates D) =
        (tailMeasure D).withDensity (fun z => ENNReal.ofReal (prefixTailDensity D g z)) := by
  let e := splitCoordinates D
  have he := measurePreserving_splitCoordinates D
  have heinv : MeasurePreserving e.symm
      ((prefixMeasure D).prod (tailMeasure D)) baseMeasure := he.symm e
  have hgp : MemLp (g ∘ e.symm) 2 ((prefixMeasure D).prod (tailMeasure D)) :=
    hg.comp_measurePreserving heinv
  have hgn : 0 ≤ᵐ[(prefixMeasure D).prod (tailMeasure D)] (g ∘ e.symm) :=
    heinv.quasiMeasurePreserving.ae hn
  have hgm : (∫ p, (g ∘ e.symm) p ∂(prefixMeasure D).prod (tailMeasure D)) = 1 := by
    exact (heinv.integral_comp e.symm.measurableEmbedding g).trans hmass
  obtain ⟨hmem, hnonneg, hmean, hnorm, hmap⟩ :=
    BiasedTailDensity.tailDensity_spec hgp hgn hgm
  have hnormeq : eLpNorm (g ∘ e.symm) 2 ((prefixMeasure D).prod (tailMeasure D)) =
      eLpNorm g 2 baseMeasure := eLpNorm_comp_measurePreserving hg.aestronglyMeasurable heinv
  refine ⟨hmem, hnonneg, hmean, hnorm.trans_eq hnormeq, ?_⟩
  have htransport := (DensityTransport.real_density_transport_ae e.measurable e.symm.measurable
    he.map_eq (Eventually.of_forall e.symm_apply_apply) hg.aemeasurable).1
  have heq : tailCoordinates D = Prod.snd ∘ e := rfl
  rw [heq, ← Measure.map_map measurable_snd e.measurable, htransport]
  exact hmap

theorem eLpNorm_prefixTailDensity_le (D : ℕ) {g : Base → ℝ}
    (hg : MemLp g 2 baseMeasure) :
    eLpNorm (prefixTailDensity D g) 2 (tailMeasure D) ≤ eLpNorm g 2 baseMeasure := by
  have heinv := (measurePreserving_splitCoordinates D).symm (splitCoordinates D)
  exact (BiasedTailDensity.eLpNorm_tailDensity_le (hg.comp_measurePreserving heinv)).trans_eq
    (eLpNorm_comp_measurePreserving hg.aestronglyMeasurable heinv)

end Invariant233.ProductModel

end

end OAI
