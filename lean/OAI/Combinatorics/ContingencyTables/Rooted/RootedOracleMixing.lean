import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleChain
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleBudget

namespace OAI

/-! # Explicit point and total-variation mixing for the selected-root grid -/

namespace ContingencyTables.RootedOracleDensity

open CommonBasesFPRAS GridBoundary CompanionFactorialApplication
open CompanionOracleDensity (dimension height binWidth height_positive oracle_grid_card
  mixingConstant mixingConstant_ge_one cutConstant cutConstant_lower oracleTime oracle_time_error)
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]

lemma gridWeight_bounds (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (_haH : a ≤ height A C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) :
    (2:ℝ)^(-a) ≤ gridWeight A R C a z v ∧ gridWeight A R C a z v ≤ 1 := by
  have hD := D_bounds A R C hC z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hh : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hh := (v i).property.2; omega)
      exact hh.trans hKB)
  have hH := height_positive A C hC
  have he0 : 0 ≤ a/height A C*D A R C z (realCorner v) :=
    mul_nonneg (div_nonneg ha hH.le) hD.1
  have he1 : a/height A C*D A R C z (realCorner v) ≤ a := by
    calc
      _ ≤ a/height A C*height A C :=
        mul_le_mul_of_nonneg_left hD.2 (div_nonneg ha hH.le)
      _ = a := div_mul_cancel₀ a hH.ne'
  have hf0 : (0:ℤ) ≤ ⌊a/height A C*D A R C z (realCorner v)⌋ :=
    Int.floor_nonneg.mpr he0
  have hf1 := (Int.floor_le (a/height A C*D A R C z (realCorner v))).trans he1
  unfold gridWeight V DenseWeights.binWeight
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · calc
      _ ≤ (2:ℝ)^(0:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast neg_nonpos.mpr hf0)
      _ = 1 := Real.rpow_zero _

lemma oracleChain_pi_lower (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) {K : ℕ} (hK : 1 ≤ K)
    (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    (2:ℝ)^(-a)/(K:ℝ)^dimension A ≤ (oracleChain A R C a z hK).π v := by
  let : Nonempty (Grid (I := Fin (dimension A)) K) := ⟨v⟩
  have hsumpos : 0 < ∑ w : Grid (I := Fin (dimension A)) K,gridWeight A R C a z w :=
    Finset.sum_pos (fun _ _ => DenseWeights.binWeight_pos _ _ _) Finset.univ_nonempty
  have hsum : (∑ w : Grid (I := Fin (dimension A)) K,gridWeight A R C a z w) ≤
      (K:ℝ)^dimension A := by
    calc
      _ ≤ ∑ _w : Grid (I := Fin (dimension A)) K,(1:ℝ) :=
        Finset.sum_le_sum (fun w _ => (gridWeight_bounds A R C a hC ha haH z hz hKB w).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
          oracle_grid_card,Nat.cast_pow]
  rw [oracleChain_pi]
  exact div_le_div₀ (DenseWeights.binWeight_pos _ _ _).le
    (gridWeight_bounds A R C a hC ha haH z hz hKB v).1 hsumpos hsum

theorem oracleChain_polynomial_poincare (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K)) :
    ∀ f,(oracleChain A R C a z hK).variance f ≤
      mixingConstant A K*(oracleChain A R C a z hK).energy f := by
  intro f
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  have hk : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hlo := cutConstant_lower A hK
  have hb : 2/(cutConstant A K)^2 ≤ mixingConstant A K := by
    calc
      _ ≤ 2/(1/(10000*(A.d:ℝ)^2*K))^2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_left₀ (by positivity) hlo 2
      _ = _ := by unfold mixingConstant; field_simp [hd.ne',hk.ne']
  exact (oracleChain_poincare A R C a hC ha haH z hK hPL hCheeger f).trans
    (mul_le_mul_of_nonneg_right hb (FiniteChain.energy_nonneg _ f))

/-- Pointwise relative mixing for the implemented dyadic-proposal
Metropolis chain; this also bounds total variation. -/
theorem oracleChain_point_mixing (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) {K : ℕ} (hK : 1 ≤ K)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (n : ℕ) (v w : Grid (I := Fin (dimension A)) K) :
    |(oracleChain A R C a z hK).iterate n ((oracleChain A R C a z hK).pointDensity w) v-1| ≤
      Real.exp (-(n:ℝ)/mixingConstant A K)/((2:ℝ)^(-a)/(K:ℝ)^dimension A) := by
  have hKR : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  apply FiniteChain.point_mixing_exp
  · exact mixingConstant_ge_one A hK
  · positivity
  · exact oracleChain_pi_lower A R C a hC ha haH z hz hK hKB
  · exact oracleChain_polynomial_poincare A R C a hC ha haH z hK hPL hCheeger

/-- The actual dyadic Metropolis chain attains the per-draw error used
in the evaluator's union bound at the explicit finite source schedule. -/
theorem oracleChain_scheduled_point_mixing (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a theta : ℝ)
    (hC : 0 < C) (ha : 0 ≤ a) (haH : a ≤ height A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v w : Grid (I := Fin (dimension A)) K) :
    |(oracleChain A R C a z hK).iterate (oracleTime A C K Q theta)
      ((oracleChain A R C a z hK).pointDensity w) v-1| ≤ theta/(8*Q) :=
  (oracleChain_point_mixing A R C a hC ha haH z hz hK hKB hPL hCheeger _ v w).trans
    (oracle_time_error A C a theta ha haH htheta K Q hK hQ)

theorem oracleChain_scheduled_total_variation (A : Instance I J) (R : RootedCompletion.Selection A.T) (C a theta : ℝ)
    (hC : 0 < C) (ha : 0 ≤ a) (haH : a ≤ height A C) (htheta : 0 < theta)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (K Q : ℕ) (hK : 1 ≤ K) (hQ : 0 < Q) (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (w : Grid (I := Fin (dimension A)) K) :
    let P := oracleChain A R C a z hK
    (∑ v, |P.π v*P.iterate (oracleTime A C K Q theta) (P.pointDensity w) v-P.π v|)/2 ≤
      theta/(8*Q) := by
  let P := oracleChain A R C a z hK
  have hpoint (v : Grid (I := Fin (dimension A)) K) :
      |P.π v*P.iterate (oracleTime A C K Q theta) (P.pointDensity w) v-P.π v| ≤
      P.π v*(theta/(8*Q)) := by
    calc
      _ = P.π v*|P.iterate (oracleTime A C K Q theta) (P.pointDensity w) v-1| := by
        rw [←mul_sub_one,abs_mul,abs_of_pos (P.positive v)]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (oracleChain_scheduled_point_mixing A R C a theta hC ha haH htheta z hz K Q hK hQ
          hKB hPL hCheeger v w) (P.positive v).le
  have hsum := Finset.sum_le_sum (fun v (_ : v∈Finset.univ) => hpoint v)
  rw [←Finset.sum_mul,P.normalized,one_mul] at hsum
  change _ ≤ theta/(8*Q)
  have he : (0:ℝ) ≤ theta/(8*Q) := by positivity
  linarith

end
end ContingencyTables.RootedOracleDensity

end OAI
