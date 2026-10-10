import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleFiniteStep
import OAI.Combinatorics.ContingencyTables.Counting.CompanionRatioSamples
import OAI.Combinatorics.ContingencyTables.Transport.FiniteLawMoments
import OAI.Combinatorics.ContingencyTables.Transport.FiniteBiasedAverages

namespace OAI

/-! # Concrete rational observations of the companion annealing ratios -/

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS ResidualMixture FirstSuccess
open FiniteLawMoments FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

private lemma floor_step (x q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ⌊x+q⌋=⌊x⌋ ∨ ⌊x+q⌋=⌊x⌋+1 := by
  have hlo := Int.floor_mono (show x ≤ x+q by linarith)
  have hhi := Int.floor_mono (show x+q ≤ x+1 by linarith)
  rw [Int.floor_add_one] at hhi
  omega

/-- The actual phase observable takes exactly the two source values,
since one annealing step changes its integer exponent by zero or one. -/
theorem ratioObservable_cases (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℝ) (hC : 0 < C)
    (a : ℕ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    ratioObservable A R C a z v=1 ∨ ratioObservable A R C a z v=1/2 := by
  have hD := D_bounds A R C hC z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hh : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hh := (v i).property.2; omega)
      exact hh.trans hKB)
  let q := D A R C z (realCorner v)/height A C
  have hq0 : 0 ≤ q := div_nonneg hD.1 (height_positive A C hC).le
  have hq1 : q ≤ 1 := (div_le_one (height_positive A C hC)).mpr hD.2
  let x := (a:ℝ)/height A C*D A R C z (realCorner v)
  have he : ((a:ℝ)+1)/height A C*D A R C z (realCorner v)=x+q := by
    dsimp only [x,q]
    ring
  have hr : ratioObservable A R C a z v=(2:ℝ)^(-((⌊x+q⌋:ℤ):ℝ)+((⌊x⌋:ℤ):ℝ)) := by
    unfold ratioObservable gridWeight V DenseWeights.binWeight
    rw [he,←Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    congr 1
    change -((⌊x+q⌋:ℤ):ℝ)- -((⌊x⌋:ℤ):ℝ)=_
    ring
  rcases floor_step x q hq0 hq1 with hf|hf
  · left
    rw [hr,hf]
    simp
  · right
    rw [hr,hf]
    have hh : -(((⌊x⌋:ℤ)+1:ℤ):ℝ)+((⌊x⌋:ℤ):ℝ)=(-1:ℝ) := by
      push_cast
      ring
    rw [hh]
    norm_num

def rationalRatioObservable (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) : ℚ :=
  rationalGridWeight A R C (a+1) z v/rationalGridWeight A R C a z v

lemma rationalRatioObservable_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) :
    (rationalRatioObservable A R C a z v:ℝ)=ratioObservable A R C a z v := by
  simp only [rationalRatioObservable,Rat.cast_div,rationalGridWeight_cast,Nat.cast_add,
    Nat.cast_one,ratioObservable]

lemma ratioObservable_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℝ) (hC : 0 < C)
    (a : ℕ) (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    1/2 ≤ ratioObservable A R C a z v ∧ ratioObservable A R C a z v ≤ 1 := by
  rcases ratioObservable_cases A R C hC a z hz hKB v with h|h <;> rw [h] <;> norm_num

lemma ratioMean_stationary (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K) :
    expectation (oracleStationaryLaw A R C a z hK) (ratioObservable A R C a z)=ratioMean A R C a z K := by
  unfold expectation ratioMean
  apply Finset.sum_congr rfl
  intro v _
  rw [oracleStationaryLaw_cast,oracleChain_pi]
  rfl

lemma ratioMean_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    {K : ℕ} (hK : 1 ≤ K) (hKB : (K:ℝ) ≤ binWidth A C) :
    1/2 ≤ ratioMean A R C a z K ∧ ratioMean A R C a z K ≤ 1 := by
  rw [←ratioMean_stationary A R C a z hK]
  exact expectation_bounds _ _ _ _ (ratioObservable_bounds A R C (by exact_mod_cast hC) a z hz hKB)

def ratioSample (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) (bits : RatioWords A C n) : ℚ :=
  rationalRatioObservable A R C a z (wordWalk (oracleBitStep A R C a z) v n bits)

lemma ratioSample_cast (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) (bits : RatioWords A C n) :
    (ratioSample A R C a z v n bits:ℝ)=
      ratioObservable A R C a z (wordWalk (oracleBitStep A R C a z) v n bits) :=
  rationalRatioObservable_cast A R C a z _

lemma ratioSample_mean (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (z : View A → ℕ)
    {K : ℕ} (v : Grid (I := Fin (dimension A)) K) (n : ℕ) :
    uniformAverage (fun bits : RatioWords A C n => (ratioSample A R C a z v n bits:ℝ))=
      expectation (oracleBitWalkLaw A R C a z v n) (ratioObservable A R C a z) := by
  simp_rw [ratioSample_cast]
  exact word_expectation (wordWalk (oracleBitStep A R C a z) v n) _

/-- The actual finite walk has small expectation bias for the literal
ratio of consecutive normalizers. -/
theorem ratioSample_mean_bias (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    |uniformAverage (fun bits : RatioWords A C (oracleTime A C K Q theta) =>
      (ratioSample A R C a z v (oracleTime A C K Q theta) bits:ℝ))-ratioMean A R C a z K| ≤
      theta/(4*Q) := by
  rw [ratioSample_mean,←ratioMean_stationary A R C a z hK]
  have hb := expectation_difference
    (oracleBitWalkLaw A R C a z v (oracleTime A C K Q theta))
    (oracleStationaryLaw A R C a z hK) (ratioObservable A R C a z) 1 (fun w => by
      have hw := ratioObservable_bounds A R C (by exact_mod_cast hC) a z hz hKB w
      rw [abs_of_nonneg (by linarith : 0 ≤ ratioObservable A R C a z w)]
      exact hw.2)
  have hm := oracleBitWalkLaw_variation A R C a theta hC haH htheta z hz K Q hK hQ
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
theorem ratioSamples_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℕ) (theta : ℝ)
    (hC : 0 < C) (haH : a ≤ rationalHeight A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q N : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hN : 0 < N)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : Fin N → RatioWords A C (oracleTime A C K Q theta) =>
      if theta*ratioMean A R C a z K <
        |sampleAverage (fun bits => (ratioSample A R C a z v (oracleTime A C K Q theta) bits:ℝ))
          N draws-ratioMean A R C a z K| then (1:ℝ) else 0) ≤ 16/(N*theta^2) := by
  let g := fun bits : RatioWords A C (oracleTime A C K Q theta) =>
    (ratioSample A R C a z v (oracleTime A C K Q theta) bits:ℝ)
  have hg (bits : RatioWords A C (oracleTime A C K Q theta)) : 0 ≤ g bits ∧ g bits ≤ 1 := by
    dsimp only [g]
    rw [ratioSample_cast]
    have hh := ratioObservable_bounds A R C (by exact_mod_cast hC) a z hz hKB
      (wordWalk (oracleBitStep A R C a z) v (oracleTime A C K Q theta) bits)
    exact ⟨by linarith,hh.2⟩
  have hr := ratioMean_bounds A R C a hC z hz hK hKB
  have hQR : (1:ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
  have hb : |uniformAverage g-ratioMean A R C a z K| ≤ theta*ratioMean A R C a z K/2 := by
    have hb := ratioSample_mean_bias A R C a theta hC haH htheta z hz K Q hK hQ hKB hPL hCheeger v
    have h1 : theta/(4*(Q:ℝ)) ≤ theta/4 := by
      apply div_le_div_of_nonneg_left htheta.le (by norm_num)
      nlinarith
    exact hb.trans (h1.trans (by nlinarith [hr.1]))
  have hh := biased_target_failure g 1 (ratioMean A R C a z K) theta hg
    (by linarith [hr.1]) htheta hb N hN
  apply hh.trans
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hs : (theta/2)^2 ≤ (theta*ratioMean A R C a z K)^2 := by
    apply (sq_le_sq₀ (by positivity) (mul_nonneg htheta.le (by linarith [hr.1]))).mpr
    nlinarith [hr.1]
  calc
    4*1^2/((N:ℝ)*(theta*ratioMean A R C a z K)^2) ≤ 4/(N*(theta/2)^2) :=
      div_le_div₀ (by norm_num) (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left hs hNR.le)
    _ = _ := by field_simp [hNR.ne',htheta.ne']; ring

end

end ContingencyTables.RootedOracleDensity

end OAI
