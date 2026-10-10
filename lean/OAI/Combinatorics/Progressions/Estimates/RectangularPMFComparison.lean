import OAI.Combinatorics.Progressions.Sampling.ControlledJointGrid

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem rectangularPMF_retained_error {I Z Y : Type*} [Fintype I]
    {J : I → Type*} [∀ i, Fintype (J i)]
    [MeasurableSpace Z] [MeasurableSpace Y]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (p : ∀ i, PMF (J i → ℤ)) (q : ∀ i, (J i → ℤ) → ℝ)
    (a S : ∀ i, J i → ℝ) (hS : ∀ i j, 1 ≤ S i j)
    (R E : I → ℝ) (hR : ∀ i, 0 ≤ R i) (hE : ∀ i, 0 ≤ E i)
    (hq0 : ∀ i v, 0 ≤ q i v)
    (hp : ∀ i v, v ∉ rectangularWeightIndices (a i) (S i) (R i) → p i v = 0)
    (hq : ∀ i v, v ∉ rectangularWeightIndices (a i) (S i) (R i) → q i v = 0)
    (he : ∀ i v, |(∏ j, S i j) * (p i v).toReal - q i v| ≤ E i)
    (hsmall : (∑ i, (2 * R i + 1) ^ Fintype.card (J i) * E i) ≤ 1)
    (T : Z × (∀ i, J i → ℤ) → Y) (hT : Measurable T)
    (φ : Y → ℝ) (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ y, ‖φ y‖ ≤ B) :
    |(∫ y, φ y ∂(μ.prod (Measure.pi (fun i => (p i).toMeasure))).map T) -
      ∫ y, φ y ∂(μ.prod (realDensityMeasure
        (Measure.pi (fun i => (Measure.count : Measure (J i → ℤ))))
        (fun x => ∏ i, q i (x i) / (∏ j, S i j)))).map T| ≤
      B * (2 * ∑ i, (2 * R i + 1) ^ Fintype.card (J i) * E i) := by
  have hg (i) : Integrable (fun v => q i v / (∏ j, S i j)) Measure.count :=
    count_integrable_of_zero_off_finset (rectangularWeightIndices (a i) (S i) (R i))
      _ (fun v hv => by rw [hq i v hv, zero_div])
  apply independentPMF_retained_grid_error μ p _ hg
    (fun i v => div_nonneg (hq0 i v)
      (Finset.prod_nonneg (fun j _ => zero_le_one.trans (hS i j))))
    _ _ hsmall T hT φ hφ hB hb
  intro i
  exact rectangular_count_density_l1 (a i) (S i) (hS i) (hR i) (hE i)
    (fun v => (p i v).toReal) (q i)
    (fun v hv => by rw [hp i v hv, ENNReal.toReal_zero]) (hq i) (he i)

end Erdos3

end

end OAI
