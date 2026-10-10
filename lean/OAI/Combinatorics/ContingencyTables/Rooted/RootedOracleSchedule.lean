import OAI.Combinatorics.ContingencyTables.Rooted.RootedCorrectionSamples
import OAI.Combinatorics.ContingencyTables.Rooted.RootedRatioSamples
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleSchedule

namespace OAI

/-! # Explicit accuracy and sample-count parameters for the weight oracle -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The concrete correction schedule discharges both arithmetic error
allowances; only the named published PL/Cheeger inputs remain. -/
theorem scheduled_correction_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a j : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (delta failure : ℚ)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) (hfailure : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : Fin (sampleCount j delta failure) →
        (Fin (oracleIntegerBits A C (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta)) → Bool) =>
      if (delta:ℝ)*correctionMean A R C a z K hK hW <
        |sampleAverage (fun bits =>
          (correctionSample A R C a z K hK hW (roundingTolerance delta) v
            (oracleTime A C K 1 (correctionTheta delta)) (offsetAccuracy A delta) bits:ℝ))
          (sampleCount j delta failure) draws-correctionMean A R C a z K hK hW| then (1:ℝ) else 0) ≤
      (failure:ℝ)/(4*((j:ℝ)+1)) := by
  have hd : (0:ℝ) < delta := by exact_mod_cast hdelta
  have hs : (0:ℚ) < roundingTolerance delta := by unfold roundingTolerance; positivity
  have hsHalf : roundingTolerance delta ≤ 1/2 := by unfold roundingTolerance; linarith
  have hsDelta : (roundingTolerance delta:ℝ) ≤ (delta:ℝ)/4 := by
    simp only [roundingTolerance,Rat.cast_div,Rat.cast_ofNat,le_refl]
  exact (correctionSamples_failure A R C a (correctionTheta delta) delta hC haH
    (by unfold correctionTheta; positivity) hd z hz K 1 (offsetAccuracy A delta)
    (sampleCount j delta failure) hK (by decide) hW (sampleCount_positive j delta failure hdelta hfailure)
    hB (roundingTolerance delta) hs hsHalf hsDelta (by simpa only [Nat.cast_one] using correction_noise_budget A delta hdelta)
    hPL hCheeger v).trans (sampleCount_budget j delta failure hdelta hfailure)


theorem scheduled_ratio_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a j : ℕ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (delta failure : ℚ)
    (hdelta : 0 < delta) (hfailure : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K : ℕ) (hK : 1 ≤ K) (hB : (K:ℝ)=binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : Fin (sampleCount j delta failure) →
        RatioWords A C (oracleTime A C K 1 delta) =>
      if (delta:ℝ)*ratioMean A R C a z K <
        |sampleAverage (fun bits => (ratioSample A R C a z v (oracleTime A C K 1 delta) bits:ℝ))
          (sampleCount j delta failure) draws-ratioMean A R C a z K| then (1:ℝ) else 0) ≤
      (failure:ℝ)/(4*((j:ℝ)+1)) := by
  have hd : (0:ℝ) < delta := by exact_mod_cast hdelta
  have hn := sampleCount_positive j delta failure hdelta hfailure
  have hh := ratioSamples_failure A R C a delta hC haH hd z hz K 1 (sampleCount j delta failure)
    hK (by decide) hn hB.le hPL hCheeger v
  apply hh.trans
  calc
    16/((sampleCount j delta failure:ℝ)*(delta:ℝ)^2) ≤
        16384/((sampleCount j delta failure:ℝ)*(delta:ℝ)^2) :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    _ ≤ _ := sampleCount_budget j delta failure hdelta hfailure

end

end ContingencyTables.RootedOracleDensity

end OAI
