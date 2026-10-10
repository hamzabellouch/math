import OAI.NumberTheory.CubicMoment.Estimates.HeckeZeroFreePair

namespace OAI

/-! Polynomial and logarithmic conductor-height bounds for the actual
normalized Hecke disks. The constants depend only on the fixed ideal lattice. -/
noncomputable section
namespace CubicFirstMoment

def heckeDiskPolynomialConstant : ℝ := 2+32*(9/2:ℝ)^4*idealZetaTwo^2

lemma heckeDiskPolynomialConstant_gt_one : 1 < heckeDiskPolynomialConstant := by
  have h : 0 ≤ 32*(9/2:ℝ)^4*idealZetaTwo^2 := by positivity
  unfold heckeDiskPolynomialConstant
  linarith

theorem normalizedHeckeDiskBound_polynomial {A k u t : ℝ} {ε : ℂ}
    (hA : 0 < A) (hk : 0 ≤ k) (hε : ‖ε‖ ≤ 1) (hu : 1 ≤ u)
    (huA : A ≤ u) (huk : k+7 ≤ u) (hut : 4+|t| ≤ u) :
    normalizedHeckeDiskBound A k ε t ≤ heckeDiskPolynomialConstant*u^12 := by
  have hS := idealZetaTwo_pos
  have hu0 : 0 ≤ u := by linarith
  have hpA := pow_le_pow_left₀ hA.le huA 4
  have hpk := pow_le_pow_left₀ (show 0 ≤ k+7 by linarith) huk 4
  have hpt := pow_le_pow_left₀ (show 0 ≤ 4+|t| by positivity) hut 4
  have hu8 : 1 ≤ u^8 := one_le_pow₀ hu
  have hu12 : 1 ≤ u^12 := one_le_pow₀ hu
  have hprod : ‖ε‖*A^4*(k+7)^4*idealZetaTwo ≤ idealZetaTwo*u^8 := by
    calc
      ‖ε‖*A^4*(k+7)^4*idealZetaTwo ≤ 1*u^4*u^4*idealZetaTwo := by gcongr
      _ = _ := by ring
  have hinner : idealZetaTwo+‖ε‖*A^4*(k+7)^4*idealZetaTwo ≤
      2*idealZetaTwo*u^8 := by
    have hscale := mul_le_mul_of_nonneg_left hu8 hS.le
    nlinarith
  calc
    normalizedHeckeDiskBound A k ε t ≤
        2+idealZetaTwo*(2*idealZetaTwo*u^8*16*(9/2:ℝ)^4)*u^4 := by
      dsimp only [normalizedHeckeDiskBound,heckeZeroFreeMajorant]
      gcongr
    _ = 2+(32*(9/2:ℝ)^4*idealZetaTwo^2)*u^12 := by ring
    _ ≤ heckeDiskPolynomialConstant*u^12 := by
      unfold heckeDiskPolynomialConstant
      nlinarith

theorem normalizedHeckeDiskBound_log {A k u t : ℝ} {ε : ℂ}
    (hA : 0 < A) (hk : 0 ≤ k) (hε : ‖ε‖ ≤ 1) (hu : 1 ≤ u)
    (huA : A ≤ u) (huk : k+7 ≤ u) (hut : 4+|t| ≤ u) :
    Real.log (normalizedHeckeDiskBound A k ε t) ≤
      Real.log heckeDiskPolynomialConstant+12*Real.log u := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hC : 0 < heckeDiskPolynomialConstant :=
    zero_lt_one.trans heckeDiskPolynomialConstant_gt_one
  have h := Real.log_le_log (zero_lt_one.trans (normalizedHeckeDiskBound_gt_one A k ε t))
    (normalizedHeckeDiskBound_polynomial hA hk hε hu huA huk hut)
  simpa only [Real.log_mul hC.ne' (pow_pos hu0 12).ne',Real.log_pow,Nat.cast_ofNat] using h

def heckePairLogConstant : ℝ :=
  (1+3*principalPoleConstant+1/principalPoleRadius+
    5*(diskLogDerivativeConstant/3)*Real.log heckeDiskPolynomialConstant)/Real.log 10+
      20*diskLogDerivativeConstant

lemma heckePairLogConstant_pos : 0 < heckePairLogConstant := by
  have hP := principalPoleConstant_pos
  have hR := principalPoleRadius_pos
  have hD := diskLogDerivativeConstant_pos
  have hC := Real.log_pos heckeDiskPolynomialConstant_gt_one
  have h10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  unfold heckePairLogConstant
  positivity

theorem heckePairZeroFreeError_log {A A2 k k2 u t : ℝ} {ε ε2 : ℂ}
    (hA : 0 < A) (hA2 : 0 < A2) (hk : 0 ≤ k) (hk2 : 0 ≤ k2)
    (hε : ‖ε‖ ≤ 1) (hε2 : ‖ε2‖ ≤ 1) (hu : 10 ≤ u)
    (huA : A ≤ u) (huA2 : A2 ≤ u) (huk : k+7 ≤ u) (huk2 : k2+7 ≤ u)
    (hut : 4+|t| ≤ u) (hut2 : 4+|2*t| ≤ u) :
    heckePairZeroFreeError (normalizedHeckeDiskBound A k ε t)
      (normalizedHeckeDiskBound A2 k2 ε2 (2*t)) ≤ heckePairLogConstant*Real.log u := by
  have hu1 : 1 ≤ u := by linarith
  have h1 := normalizedHeckeDiskBound_log hA hk hε hu1 huA huk hut
  have h2 := normalizedHeckeDiskBound_log hA2 hk2 hε2 hu1 huA2 huk2 hut2
  have hD := diskLogDerivativeConstant_pos
  have hR := principalPoleRadius_pos
  have hP := principalPoleConstant_pos
  have hC := Real.log_pos heckeDiskPolynomialConstant_gt_one
  have h10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hlu := Real.log_le_log (by norm_num : (0:ℝ)<10) hu
  let K : ℝ := 1+3*principalPoleConstant+1/principalPoleRadius+
    5*(diskLogDerivativeConstant/3)*Real.log heckeDiskPolynomialConstant
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs : K ≤ (K/Real.log 10)*Real.log u := by
    calc
      K=(K/Real.log 10)*Real.log 10 := by field_simp
      _ ≤ (K/Real.log 10)*Real.log u := by gcongr
  have hb : heckePairZeroFreeError (normalizedHeckeDiskBound A k ε t)
      (normalizedHeckeDiskBound A2 k2 ε2 (2*t)) ≤ K+20*diskLogDerivativeConstant*Real.log u := by
    unfold heckePairZeroFreeError
    dsimp [K]
    nlinarith
  unfold heckePairLogConstant
  dsimp [K] at hs hb
  nlinarith

end CubicFirstMoment

end

end OAI
