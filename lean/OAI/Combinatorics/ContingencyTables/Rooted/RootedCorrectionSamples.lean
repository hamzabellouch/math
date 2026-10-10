import OAI.Combinatorics.ContingencyTables.Rooted.RootedCorrectionArithmetic
import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawRelativeError
import OAI.Combinatorics.ContingencyTables.Transport.FiniteBiasedAverages

namespace OAI

/-! # Confidence for the actual rational correction samples -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def correctionMean (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) : ℝ :=
  expectation (stationaryIntegerLaw A R C a z K hK hW) (correction A R C a z K (by omega))

lemma correctionMean_eq (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) :
    correctionMean A R C a z K hK hW=
      ∑ f : FreeIndex A.small A.T A.b,
        correctedMass A R C a z K (by omega) f*correction A R C a z K (by omega) f := by
  unfold correctionMean expectation
  simp_rw [stationaryIntegerLaw_cast]

lemma correctionMean_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (haH : a ≤ rationalHeight A C) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=binWidth A C) :
    1/8 ≤ correctionMean A R C a z K hK hW ∧ correctionMean A R C a z K hK hW ≤ 4 := by
  have haHR : (a:ℝ) ≤ height A C := by rw [←rationalHeight_cast]; exact_mod_cast haH
  exact expectation_bounds _ _ _ _ (correction_bounds A R C a (by exact_mod_cast hC)
    (Nat.cast_nonneg _) haHR z K (by omega) hW hB)

def correctionSample (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (sigma : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ)
    (bits : Fin (oracleIntegerBits A C n h) → Bool) : ℚ :=
  computedCorrection A R C a z K (by omega) sigma (oracleIntegerDraw A R C a z K hK hW v n h bits)

lemma correctionSample_mean (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W) (sigma : ℚ)
    (v : Grid (I := Fin (dimension A)) K) (n h : ℕ) :
    uniformAverage (fun bits => (correctionSample A R C a z K hK hW sigma v n h bits:ℝ))=
      expectation (sampledIntegerLaw A R C a z K hK hW v n h)
        (fun f => (computedCorrection A R C a z K (by omega) sigma f:ℝ)) := by
  unfold correctionSample
  rw [word_expectation (oracleIntegerDraw A R C a z K hK hW v n h)
    (fun f => (computedCorrection A R C a z K (by omega) sigma f:ℝ)),oracleIntegerDraw_law]

/-- Both finite sampling error and deterministic rational power error
are bounded relative to the literal correction mean. -/
theorem correctionSample_mean_bias (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q h : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (sigma : ℚ) (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1/2)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    |uniformAverage (fun bits =>
      (correctionSample A R C a z K hK hW sigma v (oracleTime A C K Q theta) h bits:ℝ))-
        correctionMean A R C a z K hK hW| ≤
      16*(theta/(8*Q)+(A.d:ℝ)/(2:ℝ)^(4*(h+A.d)))+
        (sigma:ℝ)*correctionMean A R C a z K hK hW := by
  let g := fun f => (computedCorrection A R C a z K (by omega) sigma f:ℝ)
  let p := sampledIntegerLaw A R C a z K hK hW v (oracleTime A C K Q theta) h
  let q := stationaryIntegerLaw A R C a z K hK hW
  have hsample : |expectation p g-expectation q g| ≤
      16*(theta/(8*Q)+(A.d:ℝ)/(2:ℝ)^(4*(h+A.d))) := by
    have he := expectation_difference p q g 8 (fun f => by
      have hh := computedCorrection_bounds A R C a hC haH z K (by omega) hW hB sigma hsigma hsigmaHalf f
      rw [abs_of_nonneg (by dsimp only [g]; linarith [hh.1])]
      exact hh.2)
    have hv := sampledIntegerLaw_variation A R C a theta hC haH htheta z hz K Q h hK hQ hW
      hB.le hPL hCheeger v
    exact he.trans (by nlinarith)
  have hround : |expectation q g-correctionMean A R C a z K hK hW| ≤
      (sigma:ℝ)*correctionMean A R C a z K hK hW :=
    expectation_relative_error q (correction A R C a z K (by omega)) g sigma
      (computedCorrection_error A R C a hC haH z K (by omega) hB sigma hsigma)
  rw [correctionSample_mean]
  calc
    _ ≤ |expectation p g-expectation q g|+|expectation q g-correctionMean A R C a z K hK hW| := by
      simpa only [sub_add_sub_cancel] using abs_add_le
        (expectation p g-expectation q g) (expectation q g-correctionMean A R C a z K hK hW)
    _ ≤ _ := add_le_add hsample hround

/-- Independent finite words give confidence for the computed correction;
the displayed arithmetic tolerances are discharged by the outer schedule. -/
theorem correctionSamples_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (theta delta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta) (hdelta : 0 < delta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q h N : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hW : 100*A.d*K ≤ A.W) (hN : 0 < N)
    (hB : (K:ℝ)=binWidth A C) (sigma : ℚ) (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1/2)
    (hsigmaDelta : (sigma:ℝ) ≤ delta/4)
    (hnoise : theta/(8*Q)+(A.d:ℝ)/(2:ℝ)^(4*(h+A.d)) ≤ delta/1024)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : Fin N → (Fin (oracleIntegerBits A C (oracleTime A C K Q theta) h) → Bool) =>
      if delta*correctionMean A R C a z K hK hW <
        |sampleAverage (fun bits =>
          (correctionSample A R C a z K hK hW sigma v (oracleTime A C K Q theta) h bits:ℝ)) N draws-
            correctionMean A R C a z K hK hW| then (1:ℝ) else 0) ≤ 16384/(N*delta^2) := by
  let g := fun bits =>
    (correctionSample A R C a z K hK hW sigma v (oracleTime A C K Q theta) h bits:ℝ)
  have hg bits : 0 ≤ g bits ∧ g bits ≤ 8 := by
    have hh := computedCorrection_bounds A R C a hC haH z K (by omega) hW hB sigma hsigma hsigmaHalf
      (oracleIntegerDraw A R C a z K hK hW v (oracleTime A C K Q theta) h bits)
    exact ⟨by dsimp only [g,correctionSample]; linarith [hh.1],hh.2⟩
  have hb := correctionMean_bounds A R C a hC haH z K hK hW hB
  have hmu : 0 < correctionMean A R C a z K hK hW := by linarith [hb.1]
  have herr := correctionSample_mean_bias A R C a theta hC haH htheta z hz K Q h hK hQ hW hB sigma
    hsigma hsigmaHalf hPL hCheeger v
  have hround := mul_le_mul_of_nonneg_right hsigmaDelta hmu.le
  have hbias : |uniformAverage g-correctionMean A R C a z K hK hW| ≤
      delta*correctionMean A R C a z K hK hW/2 := by
    have hnoise' := mul_le_mul_of_nonneg_left hnoise (by norm_num : (0:ℝ) ≤ 16)
    have hlo := mul_le_mul_of_nonneg_left hb.1 hdelta.le
    dsimp only [g]
    nlinarith
  have hh := biased_target_failure g 8 _ delta hg hmu hdelta hbias N hN
  apply hh.trans
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hs : (delta/8)^2 ≤ (delta*correctionMean A R C a z K hK hW)^2 := by
    apply (sq_le_sq₀ (by positivity) (mul_nonneg hdelta.le hmu.le)).mpr
    nlinarith [hb.1]
  calc
    4*8^2/((N:ℝ)*(delta*correctionMean A R C a z K hK hW)^2) ≤ 256/(N*(delta/8)^2) :=
      div_le_div₀ (by norm_num) (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left hs hNR.le)
    _ = _ := by field_simp [hNR.ne',hdelta.ne']; ring

end

end ContingencyTables.RootedOracleDensity

end OAI
