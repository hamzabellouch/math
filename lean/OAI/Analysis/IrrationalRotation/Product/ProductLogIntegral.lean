import OAI.Analysis.IrrationalRotation.Product.ProductWeightBridge

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ProductModel

theorem uniform_floorCost_integral (θ c : ℝ) (hθ : θ ∈ Ico (0 : ℝ) 1)
    (hc : 0 ≤ c) :
    (∫⁻ u : ℝ, ENNReal.ofReal (c * (⌊u + θ⌋ : ℝ))
      ∂(volume.restrict (Ico (0 : ℝ) 1))) = ENNReal.ofReal (c * θ) := by
  classical
  have heq : (fun u : ℝ ↦ ENNReal.ofReal (c * (⌊u + θ⌋ : ℝ))) =ᵐ[
      volume.restrict (Ico (0 : ℝ) 1)]
      (Ici (1 - θ)).indicator (fun _ ↦ ENNReal.ofReal c) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ico] with u hu
    rw [FloorCocycle.floor_add_eq_indicator hu.1 hu.2,
      Int.floor_eq_zero_iff.mpr hθ, Int.fract_eq_self.mpr hθ, zero_add]
    by_cases h : 1 - θ ≤ u
    · simp [h]
    · simp [h]
  have hinter : Ici (1 - θ) ∩ Ico (0 : ℝ) 1 = Ico (1 - θ) 1 := by
    ext u
    constructor
    · rintro ⟨ha, _, hb⟩
      exact ⟨ha, hb⟩
    · intro hu
      exact ⟨hu.1, by linarith [hu.1, hθ.2], hu.2⟩
  rw [lintegral_congr_ae heq, lintegral_indicator_const measurableSet_Ici,
    Measure.restrict_apply measurableSet_Ici, hinter, Real.volume_Ico]
  rw [show (1 : ℝ) - (1 - θ) = θ by ring, ← ENNReal.ofReal_mul hc]

theorem measurable_cost_summand (θ c : ℕ → ℝ) (i : ℕ) :
    Measurable (fun x : Base ↦
      ENNReal.ofReal (c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ))) := by
  have hrep : Measurable (fun x : Base ↦ circleRepresentative (x i)) :=
    ProductCocycle.measurable_representative.comp (measurable_pi_apply i)
  exact (measurable_const.mul ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
    ((hrep.add_const (θ i)).floor))).ennreal_ofReal

theorem lintegral_cost_summand (θ c : ℕ → ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i) (i : ℕ) :
    (∫⁻ x, ENNReal.ofReal (c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ))
      ∂baseMeasure) = ENNReal.ofReal (c i * θ i) := by
  have hm : Measurable (fun u : ℝ ↦ ENNReal.ofReal (c i * (⌊u + θ i⌋ : ℝ))) :=
    (measurable_const.mul ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
      ((measurable_id.add_const (θ i)).floor))).ennreal_ofReal
  calc
    _ = ∫⁻ u : ℝ, ENNReal.ofReal (c i * (⌊u + θ i⌋ : ℝ))
        ∂(volume.restrict (Ico (0 : ℝ) 1)) :=
      (CocycleSupport.measurePreserving_productRepresentative i).lintegral_comp hm
    _ = ENNReal.ofReal (c i * θ i) := uniform_floorCost_integral _ _ (hθ i) (hc i)

theorem lintegral_logarithmicCost (θ c : ℕ → ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i) :
    (∫⁻ x, logarithmicCost θ c x ∂baseMeasure) =
      ∑' i, ENNReal.ofReal (c i * θ i) := by
  unfold logarithmicCost
  rw [lintegral_tsum (fun i ↦ (measurable_cost_summand θ c i).aemeasurable)]
  exact tsum_congr (lintegral_cost_summand θ c hθ hc)

theorem hasNegInfiniteLogIntegral_iff_tsum (θ c : ℕ → ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i) :
    HasNegInfiniteLogIntegral baseMeasure (weight θ c) ↔
      (∑' i, ENNReal.ofReal (c i * θ i)) = ∞ := by
  rw [hasNegInfiniteLogIntegral_iff, lintegral_logarithmicCost θ c hθ hc]

end Invariant233.ProductModel

end OAI
