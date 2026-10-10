import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleFiniteStep
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleCorrection
import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawMoments
import OAI.Combinatorics.ContingencyTables.Transport.FiniteBiasedAverages

namespace OAI

/-! # Concrete rational observations of the companion annealing ratios -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open FiniteLawMoments FiniteIndependentAverages
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def rationalRatioObservable (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℚ :=
  rationalGridWeight A C (a+1) z v/rationalGridWeight A C a z v

lemma rationalRatioObservable_cast (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    (rationalRatioObservable A C a z v:ℝ)=ratioObservable A C a z v := by
  simp only [rationalRatioObservable,Rat.cast_div,rationalGridWeight_cast,Nat.cast_add,
    Nat.cast_one,ratioObservable]

lemma ratioObservable_bounds (A : Instance I J) (C : ℝ) (hC : 0 < C)
    (a : ℕ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    1/2 ≤ ratioObservable A C a z v ∧ ratioObservable A C a z v ≤ 1 := by
  rcases ratioObservable_cases A C hC a z hz hKB v with h|h <;> rw [h] <;> norm_num

lemma ratioMean_stationary (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) :
    expectation (oracleStationaryLaw A C a z hK) (ratioObservable A C a z)=ratioMean A C a z K := by
  unfold expectation ratioMean
  apply Finset.sum_congr rfl
  intro v _
  rw [oracleStationaryLaw_cast,oracleChain_pi]
  rfl

lemma ratioMean_bounds (A : Instance I J) (C a : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C) :
    1/2 ≤ ratioMean A C a z K ∧ ratioMean A C a z K ≤ 1 := by
  rw [←ratioMean_stationary A C a z hK]
  exact expectation_bounds _ _ _ _ (ratioObservable_bounds A C (by exact_mod_cast hC) a z hz hKB)

abbrev RatioWords (A : Instance I J) (C n : ℕ) := Fin n → Fin (oracleStepBits A C) → Bool

def ratioSample (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) (bits : RatioWords A C n) : ℚ :=
  rationalRatioObservable A C a z (wordWalk (oracleBitStep A C a z) v n bits)

lemma ratioSample_cast (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) (bits : RatioWords A C n) :
    (ratioSample A C a z v n bits:ℝ)=
      ratioObservable A C a z (wordWalk (oracleBitStep A C a z) v n bits) :=
  rationalRatioObservable_cast _ _ _ _ _

lemma ratioSample_mean (A : Instance I J) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) :
    uniformAverage (fun bits : RatioWords A C n => (ratioSample A C a z v n bits:ℝ))=
      expectation (oracleBitWalkLaw A C a z v n) (ratioObservable A C a z) := by
  simp_rw [ratioSample_cast]
  exact word_expectation (wordWalk (oracleBitStep A C a z) v n) _

/-- The actual finite walk has small expectation bias for the literal
ratio of consecutive normalizers. -/
theorem ratioSample_mean_bias (A : Instance I J) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    |uniformAverage (fun bits : RatioWords A C (oracleTime A C K Q theta) =>
      (ratioSample A C a z v (oracleTime A C K Q theta) bits:ℝ))-ratioMean A C a z K| ≤
      theta/(4*Q) := by
  rw [ratioSample_mean,←ratioMean_stationary A C a z hK]
  have hb := expectation_difference
    (oracleBitWalkLaw A C a z v (oracleTime A C K Q theta))
    (oracleStationaryLaw A C a z hK) (ratioObservable A C a z) 1 (fun w => by
      have hw := ratioObservable_bounds A C (by exact_mod_cast hC) a z hz hKB w
      rw [abs_of_nonneg (by linarith : 0 ≤ ratioObservable A C a z w)]
      exact hw.2)
  have hm := oracleBitWalkLaw_variation A C a theta hC haH htheta z hz K Q hK hQ
    hKB hPL hCheeger v
  apply hb.trans
  calc
    _ ≤ 2*1*(theta/(8*Q)) := mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by
      have hQR : (Q:ℝ)≠0 := by exact_mod_cast hQ.ne'
      field_simp [hQR]
      ring

/-- Independent Boolean arrays give an explicit confidence bound around
its exact annealing ratio, including the finite-walk mean bias. -/
theorem ratioSamples_failure (A : Instance I J) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q N : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hN : 0 < N)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : Fin N → RatioWords A C (oracleTime A C K Q theta) =>
      if theta*ratioMean A C a z K <
        |sampleAverage (fun bits => (ratioSample A C a z v (oracleTime A C K Q theta) bits:ℝ))
          N draws-ratioMean A C a z K| then (1:ℝ) else 0) ≤ 16/(N*theta^2) := by
  let g := fun bits : RatioWords A C (oracleTime A C K Q theta) =>
    (ratioSample A C a z v (oracleTime A C K Q theta) bits:ℝ)
  have hg (bits : RatioWords A C (oracleTime A C K Q theta)) : 0 ≤ g bits ∧ g bits ≤ 1 := by
    dsimp only [g]
    rw [ratioSample_cast]
    have hh := ratioObservable_bounds A C (by exact_mod_cast hC) a z hz hKB
      (wordWalk (oracleBitStep A C a z) v (oracleTime A C K Q theta) bits)
    exact ⟨by linarith,hh.2⟩
  have hr := ratioMean_bounds A C a hC z hz hK hKB
  have hQR : (1:ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hb : |uniformAverage g-ratioMean A C a z K| ≤ theta*ratioMean A C a z K/2 := by
    have hb := ratioSample_mean_bias A C a theta hC haH htheta z hz K Q hK hQ hKB hPL hCheeger v
    have h1 : theta/(4*(Q:ℝ)) ≤ theta/4 := by
      apply div_le_div_of_nonneg_left htheta.le (by norm_num)
      nlinarith
    exact hb.trans (h1.trans (by nlinarith [hr.1]))
  have hh := biased_target_failure g 1 (ratioMean A C a z K) theta hg
    (by linarith [hr.1]) htheta hb N hN
  apply hh.trans
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hs : (theta/2)^2 ≤ (theta*ratioMean A C a z K)^2 := by
    apply (sq_le_sq₀ (by positivity) (mul_nonneg htheta.le (by linarith [hr.1]))).mpr
    nlinarith [hr.1]
  calc
    4*1^2/((N:ℝ)*(theta*ratioMean A C a z K)^2) ≤ 4/(N*(theta/2)^2) :=
      div_le_div₀ (by norm_num) (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left hs hNR.le)
    _ = _ := by field_simp [hNR.ne',htheta.ne']; ring

end

end ContingencyTables.CompanionOracleDensity

end OAI
