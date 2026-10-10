import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleMixing

namespace OAI

/-! # The explicit finite mixing schedule of the companion evaluator -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication GridBoundary CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma oracle_min_mass_exponential (A : Instance I J) (C a : ℝ)
    (ha : 0 ≤ a) (haH : a ≤ height A C) {K : ℕ} (hK : 1 ≤ K) :
    Real.exp (-(height A C+(A.d:ℝ)*K)) ≤ (2:ℝ)^(-a)/(K:ℝ)^dimension A := by
  have hKR : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hl2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hlK : Real.log (K:ℝ) ≤ K := by
    linarith [Real.log_le_sub_one_of_pos hKR]
  have hdim : (dimension A:ℝ) ≤ A.d := by
    exact_mod_cast ForestScaledPenalty.free_card_le A
  have hsum : a*Real.log 2+(dimension A:ℝ)*Real.log (K:ℝ) ≤
      height A C+(A.d:ℝ)*K := by
    have h1 := mul_le_mul_of_nonneg_left hl2 ha
    have h2 := mul_le_mul_of_nonneg_left hlK (Nat.cast_nonneg (dimension A): (0:ℝ) ≤ dimension A)
    have h3 := mul_le_mul_of_nonneg_right hdim hKR.le
    linarith
  have hpow : (K:ℝ)^dimension A=Real.exp ((dimension A:ℝ)*Real.log (K:ℝ)) := by
    rw [Real.exp_nat_mul,Real.exp_log hKR]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),hpow,←Real.exp_sub]
  apply Real.exp_le_exp.mpr
  linarith

/-- The source uses a linear reciprocal-error allowance inside the
mixing time, avoiding any unimplemented logarithm computation. -/
def oracleTime (A : Instance I J) (C : ℝ) (K Q : ℕ) (theta : ℝ) : ℕ :=
  ⌈mixingConstant A K*(height A C+(A.d:ℝ)*K+16*Q/theta+2)⌉₊

lemma oracle_time_error (A : Instance I J) (C a theta : ℝ)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (htheta : 0 < theta)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) :
    Real.exp (-(oracleTime A C K Q theta:ℝ)/mixingConstant A K)/
      ((2:ℝ)^(-a)/(K:ℝ)^dimension A) ≤ theta/(8*Q) := by
  have hM : 0 < mixingConstant A K := lt_of_lt_of_le (by norm_num) (mixingConstant_ge_one A hK)
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQ
  have htime : height A C+(A.d:ℝ)*K+16*Q/theta+2 ≤
      (oracleTime A C K Q theta:ℝ)/mixingConstant A K := by
    apply (le_div_iff₀ hM).mpr
    rw [mul_comm]
    exact Nat.le_ceil _
  have hr : (0:ℝ) < 16*Q/theta+2 := by positivity
  have hexp : Real.exp (-(16*Q/theta+2)) ≤ 1/(16*Q/theta+2) := by
    rw [Real.exp_neg]
    have hh : 16*Q/theta+2 ≤ Real.exp (16*Q/theta+2) := by
      linarith [Real.add_one_le_exp (16*Q/theta+2)]
    simpa only [one_div] using one_div_le_one_div_of_le hr hh
  have hrecip : 1/(16*Q/theta+2) ≤ theta/(8*Q) := by
    rw [div_le_div_iff₀ hr (by positivity : (0:ℝ)<8*Q)]
    have hcancel : (16*Q/theta)*theta=16*Q := div_mul_cancel₀ _ htheta.ne'
    nlinarith
  calc
    _ ≤ Real.exp (-(oracleTime A C K Q theta:ℝ)/mixingConstant A K)/
        Real.exp (-(height A C+(A.d:ℝ)*K)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _)
        (oracle_min_mass_exponential A C a ha haH hK)
    _ = Real.exp (-(oracleTime A C K Q theta:ℝ)/mixingConstant A K+
        (height A C+(A.d:ℝ)*K)) := by rw [←Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp (-(16*Q/theta+2)) := Real.exp_le_exp.mpr (by simp only [neg_div]; linarith)
    _ ≤ theta/(8*Q) := hexp.trans hrecip

/-- The actual dyadic Metropolis chain attains the per-draw error used
in the evaluator's union bound at the explicit finite source schedule. -/
theorem oracleChain_scheduled_point_mixing (A : Instance I J) (C a theta : ℝ)
    (hC : 0 < C) (ha : 0 ≤ a) (haH : a ≤ height A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v w : Grid (I := Fin (dimension A)) K) :
    |(oracleChain A C a z hK).iterate (oracleTime A C K Q theta)
      ((oracleChain A C a z hK).pointDensity w) v-1| ≤ theta/(8*Q) :=
  (oracleChain_point_mixing A C a hC ha haH z hz hK hKB hPL hCheeger _ v w).trans
    (oracle_time_error A C a theta ha haH htheta K Q hK hQ)

theorem oracleChain_scheduled_total_variation (A : Instance I J) (C a theta : ℝ)
    (hC : 0 < C) (ha : 0 ≤ a) (haH : a ≤ height A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (w : Grid (I := Fin (dimension A)) K) :
    let P := oracleChain A C a z hK
    (∑ v, |P.π v*P.iterate (oracleTime A C K Q theta) (P.pointDensity w) v-P.π v|)/2 ≤
      theta/(8*Q) := by
  let P := oracleChain A C a z hK
  have hpoint (v : Grid (I := Fin (dimension A)) K) :
      |P.π v*P.iterate (oracleTime A C K Q theta) (P.pointDensity w) v-P.π v| ≤
      P.π v*(theta/(8*Q)) := by
    calc
      _ = P.π v*|P.iterate (oracleTime A C K Q theta) (P.pointDensity w) v-1| := by
        rw [←mul_sub_one,abs_mul,abs_of_pos (P.positive v)]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (oracleChain_scheduled_point_mixing A C a theta hC ha haH htheta z hz K Q hK hQ
          hKB hPL hCheeger v w) (P.positive v).le
  have hsum := Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hpoint v)
  rw [←Finset.sum_mul,P.normalized,one_mul] at hsum
  change _ ≤ theta/(8*Q)
  have he : (0:ℝ) ≤ theta/(8*Q) := by positivity
  linarith

end

end ContingencyTables.CompanionOracleDensity

end OAI
