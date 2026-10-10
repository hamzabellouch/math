import OAI.Geometry.RCD.Metric.ScalingFactorMassBound

namespace OAI

/-! # A pointwise kernel ratio controls the normalized interpolation density -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X] [CompactSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem scaling_kernel_product_bound (K : C(X × Y,ℝ)) (F : C(X,ℝ)) (G : C(Y,ℝ))
    (hF : ∀ x, 0 ≤ F x) (hG : ∀ y, 0 ≤ G y)
    (hrow : ∀ x, F x*(∫ y, K (x,y)*G y ∂ν)=1)
    (k : C(X,ℝ)) (l : C(Y,ℝ)) {C : ℝ}
    (hkl : ∀ x y, k x*l y ≤ C*K (x,y)) :
    (∫ x, k x*F x ∂μ)*(∫ y, l y*G y ∂ν) ≤ C := by
  have hkF : Integrable (fun x => k x*F x) μ :=
    (k.continuous.mul F.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlG : Integrable (fun y => l y*G y) ν :=
    (l.continuous.mul G.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hKG (x : X) : Integrable (fun y => K (x,y)*G y) ν :=
    ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul G.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hh (x : X) : k x*(∫ y, l y*G y ∂ν) ≤ C*(∫ y, K (x,y)*G y ∂ν) := by
    rw [← integral_const_mul,← integral_const_mul]
    apply integral_mono (hlG.const_mul (k x)) ((hKG x).const_mul C)
    intro y
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hkl x y) (hG y)
  have hp (x : X) : (∫ y, l y*G y ∂ν)*(k x*F x) ≤ C := by
    calc
      _ = F x*(k x*(∫ y, l y*G y ∂ν)) := by ring
      _ ≤ F x*(C*(∫ y, K (x,y)*G y ∂ν)) := mul_le_mul_of_nonneg_left (hh x) (hF x)
      _ = C*(F x*(∫ y, K (x,y)*G y ∂ν)) := by ring
      _ = C := by rw [hrow,mul_one]
  have hi := integral_mono (hkF.const_mul (∫ y, l y*G y ∂ν)) (integrable_const C) hp
  rw [integral_const_mul] at hi
  simpa only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul,mul_one,mul_comm]
    using hi

end RegularPointCoordinates

end

end OAI
