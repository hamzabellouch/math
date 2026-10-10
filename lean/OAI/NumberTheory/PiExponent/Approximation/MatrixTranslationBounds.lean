import OAI.NumberTheory.PiExponent.Analysis.LogTailAnalytic
import OAI.NumberTheory.PiExponent.Approximation.ApproximationCenters
import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslation

namespace OAI

namespace PiExponent.MatrixTranslationBounds

open scoped BigOperators
open RowTranslation

noncomputable def weight {σ : Type*} [Fintype σ] (w : σ → ℝ) (a : σ → ℕ) : ℝ :=
  ∑ i, w i * a i

theorem error_power_product_le {σ : Type*} [Fintype σ]
    (ε : σ → ℂ) (e : σ → ℕ) (w : σ → ℝ) (C ν : ℝ)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    (∏ i, ‖ε i‖ ^ e i) ≤ Real.exp (∑ i, (e i : ℝ) * (C - ν * w i)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀ (fun i hi => by positivity)
  intro i hi
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) (hε i) _

theorem norm_rowScalar_exp_basic {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (T : σ → ℕ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ) (C ν : ℝ)
    (hT : ∀ i, 1 ≤ T i) (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε (fun i => tail (T i) (PowerSeries.log ℂ)) β a d k‖ ≤
      Real.exp ((∑ i, a i : ℕ) * Real.log 4 +
        (∑ i, ((a i - β i - d i : ℕ) : ℝ) * (C - ν * w i)) +
          (k : ℝ) * Real.log 2) := by
  have hτ := LogTailAnalytic.norm_coeff_prod_formal_logTail_le Finset.univ T
    (fun i => (d i : ℕ)) (fun i hi => hT i) k
  apply (norm_rowScalar_le ε _ β a d k ((2 : ℝ) ^ k) hτ).trans
  calc
    _ ≤ (4 : ℝ) ^ (∑ i, a i) *
        Real.exp (∑ i, ((a i - β i - d i : ℕ) : ℝ) * (C - ν * w i)) * (2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (error_power_product_le ε _ w C ν hε) (by positivity))
        (by positivity)
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem sum_exponents_le {σ : Type*} [Fintype σ] (w : σ → ℝ) (a : σ → ℕ)
    (H ws : ℝ) (hws : 0 < ws) (hw : ∀ i, ws ≤ w i) (ha : weight w a ≤ H) :
    ((∑ i, a i : ℕ) : ℝ) ≤ H / ws := by
  apply (le_div_iff₀ hws).2
  calc
    ((∑ i, a i : ℕ) : ℝ) * ws = ∑ i, ws * (a i : ℝ) := by
      simp only [Nat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring_nf
    _ ≤ weight w a := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _))
    _ ≤ H := ha

theorem residual_exponent_identity {σ : Type*} [Fintype σ]
    (a β : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (w : σ → ℝ) (C ν : ℝ) :
    (∑ i, ((a i - β i - d i : ℕ) : ℝ) * (C - ν * w i)) =
      C * ((∑ i, (a i - β i - d i) : ℕ) : ℝ) -
        ν * weight w (fun i => a i - β i) + ν * weight w (fun i => (d i : ℕ)) := by
  simp only [weight, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_sub (Nat.le_of_lt_succ (d i).isLt)]
  ring_nf

theorem norm_rowScalar_exp_weighted {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (T : σ → ℕ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν H ws v F : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i) (ha : weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F * w i ≤ v * T i)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε (fun i => tail (T i) (PowerSeries.log ℂ)) β a d k‖ ≤
      Real.exp (-ν * weight w (fun i => a i - β i) +
        H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
  by_cases hz : PowerSeries.coeff k (∏ i, tail (T i) (PowerSeries.log ℂ) ^ (d i : ℕ)) = 0
  · simp [rowScalar, hz, Real.exp_nonneg]
  have hbudget : weight w (fun i => (d i : ℕ)) ≤ H / F := by
    have hb := tail_weight_budget Finset.univ T (fun i => (d i : ℕ))
      (fun _ => PowerSeries.log ℂ) k w v F hv.le hF (fun i hi => hTw i) hz
    have hkv : v * (k : ℝ) ≤ H := by nlinarith [(le_div_iff₀ hv).mp hk]
    have hb' : weight w (fun i => (d i : ℕ)) ≤ v * k / F := by
      simpa [weight, mul_comm] using hb
    exact hb'.trans (div_le_div_of_nonneg_right hkv hF.le)
  have hsize := sum_exponents_le w (fun i => a i) H ws hws hw ha
  have hcount : ((∑ i, (a i - β i - d i) : ℕ) : ℝ) ≤ ((∑ i, a i : ℕ) : ℝ) := by
    exact_mod_cast Finset.sum_le_sum (fun i hi => (Nat.sub_le _ _).trans (Nat.sub_le _ _))
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  apply (norm_rowScalar_exp_basic ε T β a d k w C ν hT hε).trans
  apply Real.exp_le_exp.mpr
  rw [residual_exponent_identity]
  calc
    _ ≤ (Real.log 4 + C) * ((∑ i, a i : ℕ) : ℝ) -
        ν * weight w (fun i => a i - β i) + ν * (H / F) + (H / v) * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hcount hC,
        mul_le_mul_of_nonneg_left hbudget hν,
        mul_le_mul_of_nonneg_right hk hlog2]
    _ ≤ (Real.log 4 + C) * (H / ws) -
        ν * weight w (fun i => a i - β i) + ν * (H / F) + (H / v) * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsize (add_nonneg hlog4 hC)]
    _ = _ := by ring_nf

theorem weight_sub_le_weight_tsub {σ : Type*} [Fintype σ]
    (w : σ → ℝ) (a β : σ → ℕ) (hw : ∀ i, 0 ≤ w i) :
    weight w a - weight w β ≤ weight w (fun i => a i - β i) := by
  simp only [weight, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_sub]
  apply mul_le_mul_of_nonneg_left _ (hw i)
  by_cases h : β i ≤ a i
  · rw [Nat.cast_sub h]
  · have hle : a i ≤ β i := by omega
    rw [Nat.sub_eq_zero_of_le hle, Nat.cast_zero]
    exact sub_nonpos.mpr (by exact_mod_cast hle)

theorem norm_rowScalar_exp_weight_difference {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (T : σ → ℕ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν H ws v F : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i) (ha : weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F * w i ≤ v * T i)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε (fun i => tail (T i) (PowerSeries.log ℂ)) β a d k‖ ≤
      Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
  apply (norm_rowScalar_exp_weighted ε T β a d k w C ν H ws v F
    hC hν hws hv hF hw ha hk hT hTw hε).trans
  apply Real.exp_le_exp.mpr
  have h := weight_sub_le_weight_tsub w (fun i => a i) (fun i => β i)
    (fun i => hws.le.trans (hw i))
  nlinarith [mul_le_mul_of_nonneg_left h hν]

theorem actual_error_exp {σ : Type*} (p : σ → ℤ) (q : σ → ℕ)
    (j K : ℕ) (ν : ℝ) (hK : 1 ≤ K) (hj : j ≤ K) (hν : 0 ≤ ν)
    (hq : ∀ i, 1 ≤ q i)
    (happrox : ∀ i, |Real.pi - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-ν)) :
    ∀ i, ‖(j : ℂ) * (approximatePeriod (p i) (q i) - logarithmicPeriod)‖ ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + ν) - ν * (⌈Real.log (q i)⌉₊ : ℝ)) := by
  intro i
  have h := norm_center_error_exp ν hν (hq i) hj (happrox i)
  have hKpos : (0 : ℝ) < 2 * K := by exact_mod_cast (by omega : 0 < 2 * K)
  convert h using 1
  rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hKpos]
  congr 1
  ring_nf

noncomputable def truncationOrder (F v w : ℝ) : ℕ := ⌈F * w / v⌉₊

theorem truncationOrder_pos {F v w : ℝ} (hF : 0 < F) (hv : 0 < v) (hw : 0 < w) :
    1 ≤ truncationOrder F v w := by
  exact Nat.ceil_pos.mpr (div_pos (mul_pos hF hw) hv)

theorem truncationOrder_budget {F v w : ℝ} (hv : 0 < v) :
    F * w ≤ v * truncationOrder F v w := by
  have h := Nat.le_ceil (F * w / v)
  have h' := (div_le_iff₀ hv).mp h
  simpa [truncationOrder, mul_comm] using h'

end PiExponent.MatrixTranslationBounds

end OAI
