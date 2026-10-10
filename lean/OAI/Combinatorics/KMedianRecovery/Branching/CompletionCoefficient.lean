import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.BitCount

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Categorical Comparison RadiusMenus
variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V]

lemma completionAccuracy_pos : 0 < (19/50:ℝ)-1/Real.exp 1 := by
  have h : 1/Real.exp 1 ≤ (37/100:ℝ) := by
    rw [div_le_iff₀ (Real.exp_pos 1)]
    linarith [Real.exp_one_gt_d9]
  linarith

noncomputable def completionCoefficient : ℕ :=
  stepCoefficient (19/50-1/Real.exp 1) ^ 2 * sampleCoefficient (19/50-1/Real.exp 1) +
    stepCoefficient (19/50-1/Real.exp 1)
noncomputable def precisionCoefficient : ℕ :=
  firstSize mainKappa + geometricCap mainKappa mainKappa_pos + Nat.ceil (2/mainKappa) + 7
noncomputable def recoveryCoefficient : ℕ :=
  2 * precisionCoefficient + completionCoefficient + 3

omit [Fintype V] [LinearOrder V] [PseudoMetricSpace V] in
lemma completionTapeBound_polynomial (F : Finset V) (m : ℕ) :
    completionTapeBound F m ≤ completionCoefficient * (m+F.card+1)^13 :=
  completionOracleBits_polynomial F.card m completionAccuracy_pos

omit [Fintype V] [LinearOrder V] [PseudoMetricSpace V] in
lemma integralPrecision_polynomial (D : Finset V) (Δ : ℝ) (m T : ℕ)
    (hT : 1 ≤ T) (hsize : D.card+Nat.ceil Δ ≤ T) (hm : m ≤ T) :
    integralPrecision D Δ m ≤ precisionCoefficient * T := by
  have hceil : Nat.ceil (2*(m:ℝ)/mainKappa) ≤ Nat.ceil (2/mainKappa)*m := by
    apply Nat.ceil_le.mpr
    push_cast
    calc
      _ = (2/mainKappa)*(m:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _)
  have hfloor : firstSize mainKappa + geometricCap mainKappa mainKappa_pos + 6 ≤
      (firstSize mainKappa + geometricCap mainKappa mainKappa_pos + 6)*T := by
    exact Nat.le_mul_of_pos_right _ hT
  unfold integralPrecision RadiusMenus.precisionBits thirdSize precisionCoefficient
  nlinarith [Nat.mul_le_mul_left (Nat.ceil (2/mainKappa)) hm]

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma localTapeBound_polynomial (F : Finset V) (m T : ℕ)
    (hT : 1 ≤ T) (hV : Fintype.card V ≤ T) (hm : m ≤ T) (hsize : m+F.card+1 ≤ T) :
    localTapeBound F m ≤ (completionCoefficient+3) * T^13 := by
  have hc := (completionTapeBound_polynomial F m).trans
    (Nat.mul_le_mul_left completionCoefficient (Nat.pow_le_pow_left hsize 13))
  have h1 : T ≤ T^13 := by simpa using Nat.pow_le_pow_right hT (show 1 ≤ 13 by decide)
  have h2 : T^2 ≤ T^13 := Nat.pow_le_pow_right hT (by decide)
  have hvm : Fintype.card V * m ≤ T^2 := by nlinarith [Nat.mul_le_mul hV hm]
  unfold localTapeBound
  nlinarith

omit [LinearOrder V] [PseudoMetricSpace V] in

theorem recoveryBitCount_polynomial (D F : Finset V) (Δ : ℝ) (L U n : ℕ) :
    recoveryBitCount D F Δ L U n ≤
      (L+1)*(U+1)*n*recoveryCoefficient*(Fintype.card V+Nat.ceil Δ+L+1)^13 := by
  classical
  let T := Fintype.card V+Nat.ceil Δ+L+1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hV : Fintype.card V ≤ T := by dsimp [T]; omega
  have hD : D.card+Nat.ceil Δ ≤ T := by
    have := Finset.card_le_univ D
    dsimp [T]; omega
  have hL : L ≤ T := by dsimp [T]; omega
  have h2 : T^2 ≤ T^13 := Nat.pow_le_pow_right hT (by decide)
  have hbranch (guess : RecoveryGuesses L U) :
      2*guess.1.val*integralPrecision D Δ guess.1.val + localTapeBound F guess.1.val ≤
        recoveryCoefficient*T^13 := by
    have hgL : guess.1.val ≤ L := Nat.le_of_lt_succ guess.1.isLt
    have hg : guess.1.val ≤ T := hgL.trans hL
    have hsize : guess.1.val+F.card+1 ≤ T := by
      have := Finset.card_le_univ F
      dsimp [T]; omega
    have hp := integralPrecision_polynomial D Δ guess.1.val T hT hD hg
    have hc := localTapeBound_polynomial F guess.1.val T hT hV hg hsize
    have ha : 2*guess.1.val*integralPrecision D Δ guess.1.val ≤ 2*precisionCoefficient*T^2 := by
      calc
        _ ≤ 2*T*(precisionCoefficient*T) := by gcongr
        _ = _ := by ring
    have hb := Nat.mul_le_mul_left (2*precisionCoefficient) h2
    unfold recoveryCoefficient
    nlinarith
  rw [recoveryBitCount_eq]
  calc
    _ ≤ ∑ _guess : RecoveryGuesses L U, n*(recoveryCoefficient*T^13) := by
      exact Finset.sum_le_sum (fun guess _ => Nat.mul_le_mul_left n (hbranch guess))
    _ = (L+1)*(U+1)*n*recoveryCoefficient*T^13 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
        RecoveryGuesses,smul_eq_mul]
      ring

end MetricKMedianRecovery.Sampling

end OAI
