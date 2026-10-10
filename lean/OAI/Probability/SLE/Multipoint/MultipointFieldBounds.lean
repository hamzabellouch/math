import OAI.Probability.SLE.Multipoint.MultipointRegularizedField
import OAI.Probability.SLE.Multipoint.MultipointBrownianCoefficient

namespace OAI

/-! Drift and Brownian cross bounds for the concrete regularized fields. -/

noncomputable section

namespace SLEExactGauge.Multipoint

theorem regularizedLogFactor_relative_drift
    (κ D σ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) (hD : 0 < D) (hσ : σ ≤ 1)
    (z : ℂ × ℝ) (x : ℝ) :
    logGenerator κ (regularizedLogFactor κ D σ) z x / regularizedLogFactor κ D σ z x ≤
      κ*logVelocity κ z x^2 *
        ((driftAllowance (greenExponent κ)*driftThreshold (greenExponent κ)^(-greenExponent κ))*
          branchRegulator κ D σ z -
          (negativeDrift (greenExponent κ)/2)*
            damping (greenExponent κ) (branchRegulator κ D σ z) (logAngle κ z x)) := by
  have hδ : 0 < branchRegulator κ D σ z := mul_pos hD (Real.exp_pos _)
  have hs := logAngle_sin_pos κ z x
  have hf := angularFactor_pos (p := greenExponent κ) hδ hs
  have hp : 0 < greenExponent κ := by
    unfold greenExponent
    rw [sub_pos, lt_div_iff₀ hκ]
    linarith
  have h := regularized_drift_bound hp hδ hσ hs
  have hm := mul_le_mul_of_nonneg_left h
    (mul_nonneg hκ.le (sq_nonneg (logVelocity κ z x)))
  rw [regularizedLogFactor_generator κ D σ hκ, regularizedLogFactor_eq]
  convert hm using 1
  field_simp [hf.ne', (Real.exp_pos (((greenExponent κ/2)*κ/4)*(z.2-z.1.im))).ne']

lemma regularizedLogFactor_relative_spatial
    (κ D σ : ℝ) (hD : 0 < D) (z : ℂ × ℝ) (x : ℝ) :
    deriv (regularizedLogFactor κ D σ z) x / regularizedLogFactor κ D σ z x =
      Real.sqrt κ*logVelocity κ z x *
        (angularFactorFirst (greenExponent κ) (branchRegulator κ D σ z) (logAngle κ z x) /
          angularFactor (greenExponent κ) (branchRegulator κ D σ z) (logAngle κ z x)) := by
  rw [regularizedLogFactor_spatial, regularizedLogFactor_eq]
  have hf := angularFactor_pos (p := greenExponent κ) (mul_pos hD (Real.exp_pos ((σ*κ/4)*(z.2-z.1.im))))
    (logAngle_sin_pos κ z x)
  change 0 < angularFactor (greenExponent κ) (branchRegulator κ D σ z) (logAngle κ z x) at hf
  field_simp [hf.ne', (Real.exp_pos (((greenExponent κ/2)*κ/4)*(z.2-z.1.im))).ne']

theorem regularizedLogFactor_pair_absorption
    (κ Di Dj σi σj ε : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (hDi : 0 < Di) (hDj : 0 < Dj) (hε : 0 < ε)
    (zi zj : ℂ × ℝ) (x : ℝ)
    (hi1 : branchRegulator κ Di σi zi ≤ 1)
    (hj1 : branchRegulator κ Dj σj zj ≤ 1) :
    |(deriv (regularizedLogFactor κ Di σi zi) x / regularizedLogFactor κ Di σi zi x)*
        (deriv (regularizedLogFactor κ Dj σj zj) x / regularizedLogFactor κ Dj σj zj x)| ≤
      κ*(ε*(damping (greenExponent κ) (branchRegulator κ Di σi zi) (logAngle κ zi x)*
          logVelocity κ zi x^2 +
        damping (greenExponent κ) (branchRegulator κ Dj σj zj) (logAngle κ zj x)*
          logVelocity κ zj x^2) +
        youngConstant (greenExponent κ) (angularCoefficientConstant (greenExponent κ)^2) ε *
          (branchRegulator κ Di σi zi*branchRegulator κ Dj σj zj)^(-exponent (greenExponent κ))*
            (logVelocity κ zi x*logVelocity κ zj x)) := by
  have hi : 0 < branchRegulator κ Di σi zi := mul_pos hDi (Real.exp_pos _)
  have hj : 0 < branchRegulator κ Dj σj zj := mul_pos hDj (Real.exp_pos _)
  have hsi := logAngle_sin_pos κ zi x
  have hsj := logAngle_sin_pos κ zj x
  have hfi := angularFactor_pos (p := greenExponent κ) hi hsi
  have hfj := angularFactor_pos (p := greenExponent κ) hj hsj
  have hvi := logVelocity_pos κ zi x
  have hvj := logVelocity_pos κ zj x
  have hp : 0 < greenExponent κ := by
    unfold greenExponent
    rw [sub_pos, lt_div_iff₀ hκ]
    linarith
  have h := angular_pair_absorption hp hi hi1 hj hj1 hsi hsj
    hvi hvj hε
  have hh := mul_le_mul_of_nonneg_left h hκ.le
  rw [regularizedLogFactor_relative_spatial κ Di σi hDi,
    regularizedLogFactor_relative_spatial κ Dj σj hDj]
  calc
    _ = κ*((|angularFactorFirst (greenExponent κ) (branchRegulator κ Di σi zi) (logAngle κ zi x)| /
        angularFactor (greenExponent κ) (branchRegulator κ Di σi zi) (logAngle κ zi x)*logVelocity κ zi x)*
      (|angularFactorFirst (greenExponent κ) (branchRegulator κ Dj σj zj) (logAngle κ zj x)| /
        angularFactor (greenExponent κ) (branchRegulator κ Dj σj zj) (logAngle κ zj x)*logVelocity κ zj x)) := by
      simp only [abs_mul, abs_div, abs_of_nonneg (Real.sqrt_nonneg κ),
        abs_of_pos hvi, abs_of_pos hvj, abs_of_pos hfi, abs_of_pos hfj]
      let ai := |angularFactorFirst (greenExponent κ) (branchRegulator κ Di σi zi) (logAngle κ zi x)| /
        angularFactor (greenExponent κ) (branchRegulator κ Di σi zi) (logAngle κ zi x)
      let aj := |angularFactorFirst (greenExponent κ) (branchRegulator κ Dj σj zj) (logAngle κ zj x)| /
        angularFactor (greenExponent κ) (branchRegulator κ Dj σj zj) (logAngle κ zj x)
      change Real.sqrt κ*logVelocity κ zi x*ai*(Real.sqrt κ*logVelocity κ zj x*aj) =
        κ*((ai*logVelocity κ zi x)*(aj*logVelocity κ zj x))
      calc
        _ = (Real.sqrt κ)^2*((ai*logVelocity κ zi x)*(aj*logVelocity κ zj x)) := by ring
        _ = _ := by rw [Real.sq_sqrt hκ.le]
    _ ≤ _ := hh

end SLEExactGauge.Multipoint

end

end OAI
