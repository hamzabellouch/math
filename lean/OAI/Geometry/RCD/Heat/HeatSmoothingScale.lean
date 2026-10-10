import OAI.Geometry.RCD.Heat.HeatBoundedSmoothing

namespace OAI

/-! # A scale-explicit form of bounded-data heat smoothing -/

open MeasureTheory TopologicalSpace
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

theorem heat_smoothing_constant_le {C k t T : ℝ}
    (hC : 0 ≤ C) (hk : 0 ≤ k) (ht : 0 < t) (htT : t ≤ T) :
    Real.sqrt (C^2/(2*t*Real.exp (-2*k*t))) ≤ C*Real.exp (k*T)/Real.sqrt t := by
  have hroot : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hden : 0 < 2*t*Real.exp (-2*k*t) := by positivity
  have he : Real.exp (-2*k*t)*(Real.exp (k*t))^2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    convert Real.exp_zero using 2; ring
  have htroot : (Real.sqrt t)^2 = t := Real.sq_sqrt ht.le
  have hb : C^2/(2*t*Real.exp (-2*k*t)) ≤ (C*Real.exp (k*t)/Real.sqrt t)^2 := by
    rw [div_pow,mul_pow,htroot]
    apply (div_le_div_iff₀ hden ht).mpr
    have he' : C^2*Real.exp (k*t)^2*(2*t*Real.exp (-2*k*t)) = 2*(C^2*t) := by
      calc
        _ = 2*(C^2*t)*(Real.exp (-2*k*t)*Real.exp (k*t)^2) := by ring
        _ = _ := by rw [he,mul_one]
    rw [he']
    nlinarith [mul_nonneg (sq_nonneg C) ht.le]
  have hbound := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_sq (by positivity : 0 ≤ C*Real.exp (k*t)/Real.sqrt t)] at hbound
  exact hbound.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hk)) hC)
    hroot.le)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The coefficient depends on the outer time; the singularity at zero is
only inverse square root and can therefore be integrated. -/
theorem NoncollapsedRCD.heat_bounded_gradient_scale
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    ∀ (f : Lp ℝ 2 μ) (C : ℝ≥0) (_hf : ∀ᵐ x ∂μ, |f x| ≤ C)
      (t T : ℝ) (ht : 0 < t) (_htT : t ≤ T),
      ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hX.quadratic
        (heatSobolev μ hX.quadratic t ht f) x ≤ C*Real.exp (|K| *T)/Real.sqrt t := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  dsimp only
  intro f C hf t T ht htT
  filter_upwards [hX.heat_bounded_gradient K n hn p f C hf t ht] with x hx
  exact hx.trans (heat_smoothing_constant_le C.coe_nonneg (abs_nonneg K) ht htT)

end RegularPointCoordinates

end

end OAI
