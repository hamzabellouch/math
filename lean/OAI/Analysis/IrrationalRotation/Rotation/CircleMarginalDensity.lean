import OAI.Analysis.IrrationalRotation.Rotation.CircleQuantizedMarginals
import OAI.Analysis.IrrationalRotation.Couplings.ProductDensityLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleParameterData

theorem hybrid_density_of_coordinate_budget {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (ε : ℕ → Bool) {C : ℝ}
    (hsum : Summable (fun i : ℕ => if i = 0 then 0 else 50 *
      (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
        tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))))
    (hC : (∑' i : ℕ, if i = 0 then 0 else 50 *
      (kappa (p.blockIndex i) ^ 2 / (p.m (p.blockIndex i) : ℝ) +
        tag j (p.blockIndex i) / (p.m (p.blockIndex i) : ℝ))) ≤ C) :
    ∃ H : Circle → ℝ, MemLp H 2 volume ∧ (0 ≤ᵐ[volume] H) ∧
      (∫ x, H x) = 1 ∧ eLpNorm H 2 volume ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (law p j).map (hybridPoint p hr ε) =
        volume.withDensity (fun x => ENNReal.ofReal (H x)) := by
  let : ∀ i, IsProbabilityMeasure (digitReference p hr i) :=
    digitReference_isProbabilityMeasure p hr
  have he (i : ℕ) := (digitDensity_laws hp j hr (ε i) i).2.2
  have hsE : Summable (fun i =>
      ∫ d, (digitDensity p hr j (ε i) i d - 1) ^ 2 ∂digitReference p hr i) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg (fun d => sq_nonneg _)) he hsum
  obtain ⟨H, hH, hnonneg, hmean, hnorm, hmeasure⟩ :=
    ProductDensity.exists_product_density
      (μ := fun i => digitReference p hr i)
      (h := fun i => digitDensity p hr j (ε i) i) (C := C)
      (fun i => digitDensity_memLp hp j hr (ε i) i)
      (fun i d => ((digitDensity_laws hp j hr (ε i) i).1 d).1)
      (fun i => (digitDensity_laws hp j hr (ε i) i).2.1)
      hsE ((hsE.tsum_le_tsum he hsum).trans hC)
  have htwo := MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible
  change MemLp H 2 (MixedRadix.digitLaw (MixedRadix.radices p.q) hr) at hH
  change (0 ≤ᵐ[MixedRadix.digitLaw (MixedRadix.radices p.q) hr] H) at hnonneg
  change (∫ d, H d ∂MixedRadix.digitLaw (MixedRadix.radices p.q) hr) = 1 at hmean
  change eLpNorm H 2 (MixedRadix.digitLaw (MixedRadix.radices p.q) hr) ≤ _ at hnorm
  change (MixedRadix.digitLaw (MixedRadix.radices p.q) hr).withDensity
    (fun d => ENNReal.ofReal (H d)) = _ at hmeasure
  let G : Circle → ℝ := H ∘ MixedRadix.circleCanonical (MixedRadix.radices p.q) hr
  have hcan := MixedRadix.circleCanonical_measurePreserving htwo hr
  have htransport := MixedRadix.digitLaw_circle_density_transport_ae htwo hr
    hH.aestronglyMeasurable.aemeasurable
  refine ⟨G, ?_, ?_, ?_, ?_, ?_⟩
  · exact hH.comp_measurePreserving hcan
  · change ∀ᵐ x ∂(volume : Measure Circle),
      0 ≤ H (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr x)
    exact hcan.quasiMeasurePreserving.ae (p := fun d => 0 ≤ H d) hnonneg
  · have hHm : AEStronglyMeasurable H
        ((volume : Measure Circle).map (MixedRadix.circleCanonical (MixedRadix.radices p.q) hr)) := by
      rw [hcan.map_eq]
      exact hH.aestronglyMeasurable
    have hi := integral_map hcan.measurable.aemeasurable hHm
    rw [hcan.map_eq] at hi
    exact hi.symm.trans hmean
  · exact htransport.2.le.trans hnorm
  · change (law p j).map
      (MixedRadix.circleValue ∘ hybridDigits p hr ε) = _
    rw [← Measure.map_map (MixedRadix.measurable_circleValue htwo)
      (measurable_hybridDigits hr ε), map_hybridDigits hp, ← hmeasure]
    exact htransport.1

end Invariant233.CircleCoupling

end

end OAI
