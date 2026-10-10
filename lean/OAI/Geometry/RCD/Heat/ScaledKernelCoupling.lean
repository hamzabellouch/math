import OAI.Geometry.RCD.Transport.ContinuousDensityCoupling

namespace OAI

/-! # The probability coupling constructed from kernel scaling factors -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

def scaledContinuousKernel (K : C(X × Y, ℝ)) (F : C(X, ℝ)) (G : C(Y, ℝ)) : C(X × Y, ℝ) :=
  ⟨fun z => F z.1*K z*G z.2,
    ((F.continuous.comp continuous_fst).mul K.continuous).mul (G.continuous.comp continuous_snd)⟩

omit [MeasurableSpace X] [BorelSpace X] [BorelSpace Y] [IsProbabilityMeasure ν] in
theorem scaledContinuousKernel_row (K : C(X × Y, ℝ)) (F : C(X, ℝ)) (G : C(Y, ℝ)) (x : X) :
    (∫ y, scaledContinuousKernel K F G (x,y) ∂ν)=F x*(∫ y, K (x,y)*G y ∂ν) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by change F x*K (x,y)*G y = F x*(K (x,y)*G y); ring

omit [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] [IsProbabilityMeasure μ] in
theorem scaledContinuousKernel_col (K : C(X × Y, ℝ)) (F : C(X, ℝ)) (G : C(Y, ℝ)) (y : Y) :
    (∫ x, scaledContinuousKernel K F G (x,y) ∂μ)=G y*(∫ x, K (x,y)*F x ∂μ) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by change F x*K (x,y)*G y = G y*(K (x,y)*F x); ring

theorem scaledContinuousKernel_coupling [CompactSpace X] [CompactSpace Y]
    (K : C(X × Y, ℝ)) (F : C(X, ℝ)) (G : C(Y, ℝ))
    (hK : ∀ x y, 0 ≤ K (x,y)) (hF : ∀ x, 0 ≤ F x) (hG : ∀ y, 0 ≤ G y)
    (hrow : ∀ x, F x*(∫ y, K (x,y)*G y ∂ν)=1)
    (hcol : ∀ y, G y*(∫ x, K (x,y)*F x ∂μ)=1) :
    IsProbabilityMeasure (continuousDensityCoupling μ ν (scaledContinuousKernel K F G)) ∧
      (continuousDensityCoupling μ ν (scaledContinuousKernel K F G)).map Prod.fst=μ ∧
      (continuousDensityCoupling μ ν (scaledContinuousKernel K F G)).map Prod.snd=ν := by
  have h0 : ∀ z, 0 ≤ scaledContinuousKernel K F G z :=
    fun z => mul_nonneg (mul_nonneg (hF z.1) (hK z.1 z.2)) (hG z.2)
  have hr : ∀ x, (∫ y, scaledContinuousKernel K F G (x,y) ∂ν)=1 := by
    intro x
    rw [scaledContinuousKernel_row ν K F G x,hrow]
  have hc : ∀ y, (∫ x, scaledContinuousKernel K F G (x,y) ∂μ)=1 := by
    intro y
    rw [scaledContinuousKernel_col μ K F G y,hcol]
  exact ⟨continuousDensityCoupling_probability μ ν _ h0 hr,
    continuousDensityCoupling_fst μ ν _ h0 hr,continuousDensityCoupling_snd μ ν _ h0 hc⟩

end RegularPointCoordinates

end

end OAI
