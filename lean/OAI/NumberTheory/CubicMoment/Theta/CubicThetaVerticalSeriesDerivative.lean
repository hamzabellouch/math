import OAI.NumberTheory.CubicMoment.Theta.CubicThetaVerticalTermDerivative
import Mathlib.Analysis.Calculus.SmoothSeries

namespace OAI

/-! Vertical differentiation of the actual fixed-angular theta expansion.
A local lower height bound gives a single summable majorant. -/
noncomputable section
open Set
namespace CubicFirstMoment

theorem cubicThetaAngular_vertical_hasDerivAt {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (hv : 0<v) (z : ℂ) :
    HasDerivAt (fun y => cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,y))
      (∑' n : Eisenstein,cubicThetaSeriesTermVertical (cubicThetaAngularCoefficient a ℓ) z v n) v := by
  let K := C*cubicWhittakerDerivativePowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)
  let p : ℝ := 1/3-2*((ℓ.natAbs:ℝ)+3)
  let u : Eisenstein → ℝ := fun n => (K*(v/2)^p)*norm n^(-4/3:ℝ)
  have hK : 0≤K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC
      (cubicWhittakerDerivativePowerConstant_pos (by omega : 1≤ℓ.natAbs+3)).le)
      (by positivity)) (by positivity)
  have hp : p≤0 := by
    dsimp [p]
    have hk : (0:ℝ)≤ℓ.natAbs := Nat.cast_nonneg _
    linarith
  have hu : Summable u := by
    simpa only [u,neg_div] using
      (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ)<4/3)).mul_left (K*(v/2)^p)
  have hg (n : Eisenstein) (y : ℝ) (hy : y∈Ioi (v/2)) :
      HasDerivAt (fun t => cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z t n)
        (cubicThetaSeriesTermVertical (cubicThetaAngularCoefficient a ℓ) z y n) y :=
    cubicThetaSeriesTerm_vertical_hasDerivAt _ z (lt_trans (by positivity) hy) n
  have hb (n : Eisenstein) (y : ℝ) (hy : y∈Ioi (v/2)) :
      ‖cubicThetaSeriesTermVertical (cubicThetaAngularCoefficient a ℓ) z y n‖≤u n := by
    have hy0 : 0<y := lt_trans (by positivity) hy
    have hpower : y^p≤(v/2)^p :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hy.le hp
    calc
      _ ≤ (K*y^p)*norm n^(-4/3:ℝ) :=
        cubicThetaAngular_vertical_term_bound hC ha ℓ hy0 z n
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hK)
        (Real.rpow_nonneg (norm_nonneg n) _)
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi (convex_Ioi (v/2)).isPreconnected
    hg hb (show v∈Ioi (v/2) by change v/2<v; linarith)
    (cubicThetaAngular_summable hC ha ℓ hv z) (by change v/2<v; linarith)

theorem cubicThetaAngular_vertical_deriv {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (hv : 0<v) (z : ℂ) :
    deriv (fun y => cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,y)) v=
      ∑' n : Eisenstein,cubicThetaSeriesTermVertical (cubicThetaAngularCoefficient a ℓ) z v n :=
  (cubicThetaAngular_vertical_hasDerivAt hC ha ℓ hv z).deriv

end CubicFirstMoment

end

end OAI
