import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleChain

namespace OAI

/-! # Quantitative mixing for the companion's actual evaluator grid -/

namespace ContingencyTables.CompanionOracleDensity

open CommonBasesFPRAS GridBoundary CompanionFactorialApplication
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

lemma oracle_grid_card (q K : ℕ) : Fintype.card (Grid (I := Fin q) K)=K^q := by
  have hc : Fintype.card (Set.Icc (0:ℤ) ((K:ℤ)-1))=K := by
    have hh := Int.card_fintype_Icc_of_le 0 ((K:ℤ)-1)
      (show (0:ℤ) ≤ (K:ℤ)-1+1 by omega)
    omega
  simp only [Grid,Fintype.card_fun,Fintype.card_fin,hc]

lemma gridWeight_bounds (A : Instance I J) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (_haH : a ≤ height A C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) {K : ℕ} (hKB : (K:ℝ) ≤ binWidth A C)
    (v : Grid (I := Fin (dimension A)) K) :
    (2:ℝ)^(-a) ≤ gridWeight A C a z v ∧ gridWeight A C a z v ≤ 1 := by
  have hD := D_bounds A C hC z hz (realCorner v) (by
    intro i
    constructor
    · change (0:ℝ) ≤ ((v i).val:ℝ)
      exact_mod_cast (v i).property.1
    · have hh : (realCorner v i:ℝ) ≤ K := by
        change ((v i).val:ℝ) ≤ K
        exact_mod_cast (show (v i).val ≤ (K:ℤ) by have hh := (v i).property.2; omega)
      exact hh.trans hKB)
  have hH := height_positive A C hC
  have he0 : 0 ≤ a/height A C*D A C z (realCorner v) :=
    mul_nonneg (div_nonneg ha hH.le) hD.1
  have he1 : a/height A C*D A C z (realCorner v) ≤ a := by
    calc
      _ ≤ a/height A C*height A C :=
        mul_le_mul_of_nonneg_left hD.2 (div_nonneg ha hH.le)
      _ = a := div_mul_cancel₀ a hH.ne'
  have hf0 : (0:ℤ) ≤ ⌊a/height A C*D A C z (realCorner v)⌋ :=
    Int.floor_nonneg.mpr he0
  have hf1 := (Int.floor_le (a/height A C*D A C z (realCorner v))).trans he1
  unfold gridWeight V DenseWeights.binWeight
  constructor
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  · calc
      _ ≤ (2:ℝ)^(0:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast neg_nonpos.mpr hf0)
      _ = 1 := Real.rpow_zero _

lemma oracleChain_pi_lower (A : Instance I J) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) {K : ℕ} (hK : 1 ≤ K)
    (hKB : (K:ℝ) ≤ binWidth A C) (v : Grid (I := Fin (dimension A)) K) :
    (2:ℝ)^(-a)/(K:ℝ)^dimension A ≤ (oracleChain A C a z hK).π v := by
  let : Nonempty (Grid (I := Fin (dimension A)) K) := ⟨v⟩
  have hsumpos : 0 < ∑ w : Grid (I := Fin (dimension A)) K,gridWeight A C a z w :=
    Finset.sum_pos (fun _ _ => DenseWeights.binWeight_pos _ _ _) Finset.univ_nonempty
  have hsum : (∑ w : Grid (I := Fin (dimension A)) K,gridWeight A C a z w) ≤
      (K:ℝ)^dimension A := by
    calc
      _ ≤ ∑ _w : Grid (I := Fin (dimension A)) K,(1:ℝ) :=
        Finset.sum_le_sum (fun w _ => (gridWeight_bounds A C a hC ha haH z hz hKB w).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
          oracle_grid_card,Nat.cast_pow]
  rw [oracleChain_pi]
  exact div_le_div₀ (DenseWeights.binWeight_pos _ _ _).le
    (gridWeight_bounds A C a hC ha haH z hz hKB v).1 hsumpos hsum

def mixingConstant (A : Instance I J) (K : ℕ) : ℝ := 2*(10000*(A.d:ℝ)^2*K)^2

lemma mixingConstant_ge_one (A : Instance I J) {K : ℕ} (hK : 1 ≤ K) :
    1 ≤ mixingConstant A K := by
  have hd : (1:ℝ) ≤ A.d := by exact_mod_cast A.hd
  have hk : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hd2 : (1:ℝ) ≤ (A.d:ℝ)^2 := one_le_pow₀ hd
  have hm : (1:ℝ) ≤ 10000*(A.d:ℝ)^2*K := by
    have hh := mul_le_mul hd2 hk (by norm_num : (0:ℝ) ≤ 1) (sq_nonneg (A.d:ℝ))
    nlinarith
  unfold mixingConstant
  nlinarith [sq_nonneg (10000*(A.d:ℝ)^2*K-1)]

lemma cutConstant_lower (A : Instance I J) {K : ℕ} (hK : 1 ≤ K) :
    1/(10000*(A.d:ℝ)^2*K) ≤ cutConstant A K := by
  have hd : (0:ℝ) < A.d := by exact_mod_cast (show 0 < A.d by have hh := A.hd; omega)
  have hk : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  calc
    _ ≤ 1/(2048*(A.d:ℝ)^2*K) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr; norm_num)
    _ = (1/(16*(A.d:ℝ)))/(128*(A.d:ℝ)*K) := by field_simp [hd.ne',hk.ne']; ring
    _ ≤ cutConstant A K :=
      div_le_div_of_nonneg_right (proposal_bounds A.d A.hd).2.1 (by positivity)

theorem oracleChain_polynomial_poincare (A : Instance I J) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    {K : ℕ} (hK : 1 ≤ K)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K)) :
    ∀ f,(oracleChain A C a z hK).variance f ≤
      mixingConstant A K*(oracleChain A C a z hK).energy f := by
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
  exact (oracleChain_poincare A C a hC ha haH z hK hPL hCheeger f).trans
    (mul_le_mul_of_nonneg_right hb (FiniteChain.energy_nonneg _ f))

/-- Pointwise relative mixing for the implemented dyadic-proposal
Metropolis chain; this also bounds total variation. -/
theorem oracleChain_point_mixing (A : Instance I J) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) {K : ℕ} (hK : 1 ≤ K)
    (hKB : (K:ℝ) ≤ binWidth A C)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (n : ℕ) (v w : Grid (I := Fin (dimension A)) K) :
    |(oracleChain A C a z hK).iterate n ((oracleChain A C a z hK).pointDensity w) v-1| ≤
      Real.exp (-(n:ℝ)/mixingConstant A K)/((2:ℝ)^(-a)/(K:ℝ)^dimension A) := by
  have hKR : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  apply FiniteChain.point_mixing_exp
  · exact mixingConstant_ge_one A hK
  · positivity
  · exact oracleChain_pi_lower A C a hC ha haH z hz hK hKB
  · exact oracleChain_polynomial_poincare A C a hC ha haH z hK hPL hCheeger

end

end ContingencyTables.CompanionOracleDensity

end OAI
