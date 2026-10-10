import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyBudgetBasic

namespace OAI

noncomputable section
namespace Ostmann.Characters.HistoryFrequencyBudget

private theorem self_le_exp_two_sqrt {m : ℝ} (hm : 0 < m) :
    m ≤ Real.exp (2*Real.sqrt m) := by
  have hl := Real.log_le_rpow_div hm.le (by norm_num : (0:ℝ)<1/2)
  rw [← Real.sqrt_eq_rpow] at hl
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log hm] at he
  convert he using 1
  congr 1
  ring

def nodeExponent (C D ε a m : ℝ) (j : ℕ) : ℝ :=
  Real.log (max (2*C*D) 1 * (1+linearEnvelope a j)) +
    2*ε*linearEnvelope a j*m + 2*Real.sqrt m

theorem nodeBudget_le_exp {C D ε a m : ℝ} (_hC : 0 ≤ C) (_hD : 0 < D)
    (hε : 0 ≤ ε) (ha : 0 ≤ a) (hm : 1 ≤ m) (j : ℕ) (p : List Bool) :
    C*(bound a m (j-p.length):ℝ)^ε *
      (2*D*(bound a m (j-(false::p).length):ℝ)^ε *
        (1+Real.log (bound a m (j-p.length)))) ≤
    Real.exp (nodeExponent C D ε a m j) := by
  let A := linearEnvelope a j
  let Q := max (2*C*D) 1
  have hA : 0 < A := linearEnvelope_pos ha j
  have hQ : 0 < Q := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hv (q : List Bool) : (bound a m (j-q.length):ℝ) ≤ Real.exp (A*m) :=
    (bound_le_exp _ _ _).trans (Real.exp_le_exp.mpr (exponent_le_linear ha hm (Nat.sub_le _ _)))
  have hr (q : List Bool) : (bound a m (j-q.length):ℝ)^ε ≤ Real.exp (ε*A*m) := by
    have h := Real.rpow_le_rpow (Nat.cast_nonneg _) (hv q) hε
    rw [← Real.exp_mul] at h
    convert h using 1
    congr 1
    ring
  have hpos : (0:ℝ) < bound a m (j-p.length) := by
    exact_mod_cast (bound_pos ha hm0.le _)
  have hlog : Real.log (bound a m (j-p.length)) ≤ A*m := by
    have h := Real.log_le_log hpos (hv p)
    simpa only [Real.log_exp] using h
  have hlast : 1+Real.log (bound a m (j-p.length)) ≤
      (1+A)*Real.exp (2*Real.sqrt m) := by
    calc
      _ ≤ (1+A)*m := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left (self_le_exp_two_sqrt hm0) (by positivity)
  have hnonneg : 0 ≤ 1+Real.log (bound a m (j-p.length)) := by
    have hb : (1:ℝ) ≤ bound a m (j-p.length) := by exact_mod_cast bound_pos ha hm0.le (j-p.length)
    exact add_nonneg zero_le_one (Real.log_nonneg hb)
  calc
    _ = (2*C*D)*(bound a m (j-p.length):ℝ)^ε *
        (bound a m (j-(false::p).length):ℝ)^ε *
          (1+Real.log (bound a m (j-p.length))) := by ring
    _ ≤ Q*Real.exp (ε*A*m)*Real.exp (ε*A*m)*((1+A)*Real.exp (2*Real.sqrt m)) := by
      apply mul_le_mul _ hlast hnonneg (by positivity)
      apply mul_le_mul _ (hr _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
      exact mul_le_mul (le_max_left _ _) (hr _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hQ.le
    _ = Real.exp (nodeExponent C D ε a m j) := by
      unfold nodeExponent
      change _ = Real.exp (Real.log (Q*(1+A))+2*ε*A*m+2*Real.sqrt m)
      rw [Real.exp_add,Real.exp_add,Real.exp_log (by positivity : 0<Q*(1+A))]
      rw [show 2*ε*A*m = ε*A*m+ε*A*m by ring,Real.exp_add]
      ring

theorem budget_bound {C D ε a m : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (hε : 0 ≤ ε) (ha : 0 ≤ a) (hm : 1 ≤ m) (j : ℕ) :
    FrequencyTreeSum.budget (ranges a m j)
      (fun p => C*(bound a m (j-p.length):ℝ)^ε *
        (2*D*(bound a m (j-(false::p).length):ℝ)^ε *
          (1+Real.log (bound a m (j-p.length))))) j [] ≤
    Real.exp ((2:ℝ)^j*(Real.log 2+a*m+2*Real.sqrt m)+
      ((2:ℝ)^j-1)*nodeExponent C D ε a m j) := by
  apply budget_exp_bound (N:=j)
  · intro p
    have hb : (1:ℝ) ≤ bound a m (j-p.length) := by
      exact_mod_cast bound_pos ha (by linarith : 0 ≤ m) (j-p.length)
    have hl : 0 ≤ 1+Real.log (bound a m (j-p.length)) :=
      add_nonneg zero_le_one (Real.log_nonneg hb)
    positivity
  · exact nodeBudget_le_exp hC hD hε ha hm j
  · intro p hp
    simp only [ranges,hp,Nat.sub_self,signedRange_card,Nat.cast_mul,Nat.cast_ofNat]
    calc
      2*(bound a m 0:ℝ) ≤ 2*Real.exp (exponent a m 0) :=
        mul_le_mul_of_nonneg_left (bound_le_exp _ _ _) (by norm_num)
      _ = _ := by
        simp only [exponent,pow_zero,one_mul,mul_one,Real.exp_add,
          Real.exp_log (by norm_num : (0:ℝ)<2)]
        ring
  · simp

end Ostmann.Characters.HistoryFrequencyBudget

end

end OAI
