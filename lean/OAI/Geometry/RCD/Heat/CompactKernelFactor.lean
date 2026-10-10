import OAI.Geometry.RCD.Heat.ContinuousKernelLog

namespace OAI

/-! # Continuous factors integrated over compact endpoint supports -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (ν : Measure Y) [IsProbabilityMeasure ν]

omit [LocallyCompactSpace X] in
theorem compact_kernel_factor_integrable (K : C(X × Y, ℝ)) (F : C(Y, ℝ)) (x : X) :
    Integrable (fun y => K (x,y)*F y) ν :=
  ((K.continuous.comp (continuous_const.prodMk continuous_id)).mul F.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

def compactKernelFactor (K : C(X × Y, ℝ)) (F : C(Y, ℝ)) : C(X, ℝ) where
  toFun x := ∫ y, K (x,y)*F y ∂ν
  continuous_toFun := by
    have h := continuous_parametric_integral_of_continuous (μ := ν)
      (f := fun x y => K (x,y)*F y)
      (K.continuous.mul (F.continuous.comp continuous_snd)) isCompact_univ
    simpa only [Measure.restrict_univ] using h

theorem compactKernelFactor_pos (K : C(X × Y, ℝ)) (F : C(Y, ℝ))
    (hK : ∀ x y, 0 < K (x,y)) (hF : ∀ y, 0 < F y) (x : X) :
    0 < compactKernelFactor ν K F x := by
  change 0 < ∫ y, K (x,y)*F y ∂ν
  rw [integral_pos_iff_support_of_nonneg
    (fun y => (mul_pos (hK x y) (hF y)).le) (compact_kernel_factor_integrable ν K F x)]
  have hs : Function.support (fun y => K (x,y)*F y)=univ := by
    ext y
    simp only [Function.mem_support,Set.mem_univ,iff_true]
    exact (mul_pos (hK x y) (hF y)).ne'
  rw [hs]
  simp

theorem compactKernelFactor_ofReal (K : C(X × Y, ℝ)) (F : C(Y, ℝ))
    (hK : ∀ x y, 0 ≤ K (x,y)) (hF : ∀ y, 0 ≤ F y) (x : X) :
    ENNReal.ofReal (compactKernelFactor ν K F x) =
      ∫⁻ y, ENNReal.ofReal (K (x,y))*ENNReal.ofReal (F y) ∂ν := by
  change ENNReal.ofReal (∫ y, K (x,y)*F y ∂ν) = _
  rw [ofReal_integral_eq_lintegral_ofReal (compact_kernel_factor_integrable ν K F x)
    (Eventually.of_forall fun y => mul_nonneg (hK x y) (hF y))]
  exact lintegral_congr fun y => ENNReal.ofReal_mul (hK x y)

end RegularPointCoordinates

end

end OAI
