import OAI.Geometry.RCD.Heat.ContinuousKernelMarginalMass

namespace OAI

/-! # A continuous density with unit rows and columns is a coupling -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

def continuousDensityCoupling (h : C(X × Y, ℝ)) : Measure (X × Y) :=
  (μ.prod ν).withDensity (fun z => ENNReal.ofReal (h z))

theorem continuousDensityCoupling_fst [CompactSpace Y] (h : C(X × Y, ℝ))
    (h0 : ∀ z, 0 ≤ h z) (hrow : ∀ x, (∫ y, h (x,y) ∂ν)=1) :
    (continuousDensityCoupling μ ν h).map Prod.fst=μ := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA,continuousDensityCoupling,
    withDensity_apply _ (measurable_fst hA)]
  rw [show Prod.fst ⁻¹' A = A ×ˢ (univ : Set Y) by ext z; simp]
  rw [setLIntegral_prod _ (h.continuous.measurable.ennreal_ofReal.aemeasurable)]
  simp only [Measure.restrict_univ]
  have hr : ∀ x, (∫⁻ y, ENNReal.ofReal (h (x,y)) ∂ν)=1 := by
    intro x
    have hi : Integrable (fun y => h (x,y)) ν :=
      (h.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun y => h0 (x,y)),hrow]
    exact ENNReal.ofReal_one
  simp only [hr,lintegral_const,Measure.restrict_apply MeasurableSet.univ,univ_inter,one_mul]

theorem continuousDensityCoupling_snd [CompactSpace X] (h : C(X × Y, ℝ))
    (h0 : ∀ z, 0 ≤ h z) (hcol : ∀ y, (∫ x, h (x,y) ∂μ)=1) :
    (continuousDensityCoupling μ ν h).map Prod.snd=ν := by
  ext A hA
  rw [Measure.map_apply measurable_snd hA,continuousDensityCoupling,
    withDensity_apply _ (measurable_snd hA)]
  rw [show Prod.snd ⁻¹' A = (univ : Set X) ×ˢ A by ext z; simp]
  rw [setLIntegral_prod_symm _ (h.continuous.measurable.ennreal_ofReal.aemeasurable)]
  simp only [Measure.restrict_univ]
  have hc : ∀ y, (∫⁻ x, ENNReal.ofReal (h (x,y)) ∂μ)=1 := by
    intro y
    have hi : Integrable (fun x => h (x,y)) μ :=
      (h.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => h0 (x,y)),hcol]
    exact ENNReal.ofReal_one
  simp only [hc,lintegral_const,Measure.restrict_apply MeasurableSet.univ,univ_inter,one_mul]

theorem continuousDensityCoupling_probability [CompactSpace Y] (h : C(X × Y, ℝ))
    (h0 : ∀ z, 0 ≤ h z) (hrow : ∀ x, (∫ y, h (x,y) ∂ν)=1) :
    IsProbabilityMeasure (continuousDensityCoupling μ ν h) := by
  have hm := continuousDensityCoupling_fst μ ν h h0 hrow
  let : IsProbabilityMeasure ((continuousDensityCoupling μ ν h).map Prod.fst) := by
    rw [hm]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

end RegularPointCoordinates

end

end OAI
