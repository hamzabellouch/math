import OAI.Combinatorics.ContingencyTables.Counting.CompanionCorrectionSamples
import OAI.Combinatorics.ContingencyTables.Counting.CompanionRatioSamples

namespace OAI

/-! # Explicit accuracy and sample-count parameters for the weight oracle -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open FiniteLawMoments FiniteIndependentAverages
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def offsetAccuracy (A : Instance I J) (delta : ℚ) : ℕ := ⌈4096*(A.d:ℚ)/delta⌉₊

def correctionTheta (delta : ℚ) : ℝ := (delta:ℝ)/256

def roundingTolerance (delta : ℚ) : ℚ := delta/4

def sampleCount (j : ℕ) (delta failure : ℚ) : ℕ := ⌈65536*(j+1)/(failure*delta^2)⌉₊

private lemma le_two_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 0 < 2^n := pow_pos (by decide) _
    rw [pow_succ]
    omega

lemma offsetAccuracy_positive (A : Instance I J) (delta : ℚ) (hdelta : 0 < delta) :
    0 < offsetAccuracy A delta := by
  have hd : (0:ℚ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  have hh := Nat.le_ceil (4096*(A.d:ℚ)/delta)
  have hp : (0:ℚ) < offsetAccuracy A delta := lt_of_lt_of_le (by positivity) hh
  exact_mod_cast hp

lemma offsetAccuracy_error (A : Instance I J) (delta : ℚ) (hdelta : 0 < delta) :
    (A.d:ℝ)/(2:ℝ)^(4*(offsetAccuracy A delta+A.d)) ≤ (delta:ℝ)/4096 := by
  have hd : (0:ℝ) < delta := by exact_mod_cast hdelta
  have hh : (4096:ℝ)*A.d/(delta:ℝ) ≤ offsetAccuracy A delta := by
    have hb := Nat.le_ceil (4096*(A.d:ℚ)/delta)
    unfold offsetAccuracy
    exact_mod_cast hb
  have he : offsetAccuracy A delta ≤ 2^(4*(offsetAccuracy A delta+A.d)) := by
    exact (le_two_pow _).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hp : (offsetAccuracy A delta:ℝ) ≤ (2:ℝ)^(4*(offsetAccuracy A delta+A.d)) := by exact_mod_cast he
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2^(4*(offsetAccuracy A delta+A.d))) (by norm_num : (0:ℝ)<4096)]
  have hb := (div_le_iff₀ hd).mp hh
  nlinarith [mul_le_mul_of_nonneg_left hp hd.le]

lemma correction_noise_budget (A : Instance I J) (delta : ℚ) (hdelta : 0 < delta) :
    correctionTheta delta/(8*1)+(A.d:ℝ)/(2:ℝ)^(4*(offsetAccuracy A delta+A.d)) ≤
      (delta:ℝ)/1024 := by
  have hh := offsetAccuracy_error A delta hdelta
  have hd : (0:ℝ) < delta := by exact_mod_cast hdelta
  unfold correctionTheta
  linarith

lemma sampleCount_positive (j : ℕ) (delta failure : ℚ) (hdelta : 0 < delta)
    (hfailure : 0 < failure) : 0 < sampleCount j delta failure := by
  have hh := Nat.le_ceil (65536*(j+1:ℚ)/(failure*delta^2))
  have hp : (0:ℚ) < sampleCount j delta failure := lt_of_lt_of_le (by positivity) hh
  exact_mod_cast hp

/-- Every one of the j ratio averages and the final correction average
has failure at most this common share. -/
lemma sampleCount_budget (j : ℕ) (delta failure : ℚ) (hdelta : 0 < delta)
    (hfailure : 0 < failure) :
    16384/((sampleCount j delta failure:ℝ)*(delta:ℝ)^2) ≤ (failure:ℝ)/(4*((j:ℝ)+1)) := by
  have hd : (0:ℝ) < delta := by exact_mod_cast hdelta
  have hf : (0:ℝ) < failure := by exact_mod_cast hfailure
  have hN : (0:ℝ) < sampleCount j delta failure := by
    exact_mod_cast sampleCount_positive j delta failure hdelta hfailure
  have hh : (65536:ℝ)*((j:ℝ)+1)/((failure:ℝ)*(delta:ℝ)^2) ≤ sampleCount j delta failure := by
    have hb := Nat.le_ceil (65536*(j+1:ℚ)/(failure*delta^2))
    unfold sampleCount
    exact_mod_cast hb
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (sampleCount j delta failure:ℝ)*(delta:ℝ)^2)
    (by positivity : (0:ℝ) < 4*((j:ℝ)+1))]
  have hb := (div_le_iff₀ (show (0:ℝ) < (failure:ℝ)*(delta:ℝ)^2 by positivity)).mp hh
  nlinarith

/-- The concrete correction schedule discharges both arithmetic error
allowances; only the named published PL/Cheeger inputs remain. -/
theorem scheduled_correction_failure (A : Instance I J) (C a j : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (delta failure : ℚ)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) (hfailure : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : Fin (sampleCount j delta failure) →
        (Fin (oracleIntegerBits A C (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta)) → Bool) =>
      if (delta:ℝ)*correctionMean A C a z K hK hW <
        |sampleAverage (fun bits =>
          (correctionSample A C a z K hK hW (roundingTolerance delta) v
            (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta) bits:ℝ))
          (sampleCount j delta failure) draws-correctionMean A C a z K hK hW| then (1:ℝ) else 0) ≤
      (failure:ℝ)/(4*((j:ℝ)+1)) := by
  have hd : (0:ℝ) < delta := by exact_mod_cast hdelta
  have hs : (0:ℚ) < roundingTolerance delta := by unfold roundingTolerance; positivity
  have hsHalf : roundingTolerance delta ≤ 1/2 := by unfold roundingTolerance; linarith
  have hsDelta : (roundingTolerance delta:ℝ) ≤ (delta:ℝ)/4 := by
    simp only [roundingTolerance,Rat.cast_div,Rat.cast_ofNat,le_refl]
  exact (correctionSamples_failure A C a (correctionTheta delta) delta hC haH
    (by unfold correctionTheta; positivity) hd z hz K 1 (offsetAccuracy A delta)
    (sampleCount j delta failure) hK (by decide) hW (sampleCount_positive j delta failure hdelta hfailure)
    hB (roundingTolerance delta) hs hsHalf hsDelta (by simpa only [Nat.cast_one] using correction_noise_budget A delta hdelta)
    hPL hCheeger v).trans (sampleCount_budget j delta failure hdelta hfailure)


theorem scheduled_ratio_failure (A : Instance I J) (C a j : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (delta failure : ℚ)
    (hdelta : 0 < delta) (hfailure : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K : ℕ) (hK : 1 ≤ K) (hB : (K:ℝ)=binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : Fin (sampleCount j delta failure) →
        RatioWords A C (oracleTime A C K 1 delta) =>
      if (delta:ℝ)*ratioMean A C a z K <
        |sampleAverage (fun bits => (ratioSample A C a z v (oracleTime A C K 1 delta) bits:ℝ))
          (sampleCount j delta failure) draws-ratioMean A C a z K| then (1:ℝ) else 0) ≤
      (failure:ℝ)/(4*((j:ℝ)+1)) := by
  have hd : (0:ℝ) < delta := by exact_mod_cast hdelta
  have hn := sampleCount_positive j delta failure hdelta hfailure
  have hh := ratioSamples_failure A C a delta hC haH hd z hz K 1 (sampleCount j delta failure)
    hK (by decide) hn hB.le hPL hCheeger v
  apply hh.trans
  calc
    16/((sampleCount j delta failure:ℝ)*(delta:ℝ)^2) ≤
        16384/((sampleCount j delta failure:ℝ)*(delta:ℝ)^2) :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    _ ≤ _ := sampleCount_budget j delta failure hdelta hfailure

end

end ContingencyTables.CompanionOracleDensity

end OAI
