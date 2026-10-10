import OAI.NumberTheory.TotientAsymptotic.RenewalBackground

namespace OAI

/-! Numerical budgets for the ordered renewal translate. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma exists_ordered_shift_size {A c s D : ℝ}
    (hA : 0 < A) (hc : 0 < c) (hs : 0 < s) (hD : 0 < D) :
    ∃ K : ℝ,0 < K ∧ Real.exp (A-s*D*K)/(1-Real.exp (-c)) ≤ 1/2 := by
  let q := 1-Real.exp (-c)
  have hq : 0 < q := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  let K := (A+|Real.log (q/2)|+1)/(s*D)
  have hK : 0 < K := div_pos (by positivity) (mul_pos hs hD)
  refine ⟨K,hK,?_⟩
  have he : A-s*D*K= -|Real.log (q/2)|-1 := by
    dsimp [K]
    field_simp
    ring
  have hlog : A-s*D*K ≤ Real.log (q/2) := by
    rw [he]
    have hh := neg_abs_le (Real.log (q/2))
    linarith only [hh]
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by positivity : 0 < q/2)] at hexp
  apply (div_le_iff₀ hq).mpr
  change Real.exp (A-s*D*K) ≤ (1/2:ℝ)*q
  linarith only [hexp]

lemma renewal_top_cost_nonneg (n : ℕ) : 0 ≤ g (n+1)-a (n+1) := by
  have he := renewal_reverse_sum (N:=n+1) (i:=0) (by omega)
  simp only [Nat.sub_zero] at he
  rw [←he]
  apply Finset.sum_nonneg
  intro j hj
  split_ifs with hj0
  · exact mul_nonneg (a_pos (by omega)).le (g_pos _).le
  · exact le_rfl

lemma renewal_shift_cost {n : ℕ} (hn : 0 < n) {B K : ℝ}
    (hB : 0 < B) (hK : 0 < K) :
    let t := K*B/((n:ℝ)*g (n+1))
    0 < t ∧ 0 ≤ t*(g (n+1)-a (n+1)) ∧
      t*(g (n+1)-a (n+1)) ≤ K*B/n := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  dsimp only
  have ht : 0 < K*B/((n:ℝ)*g (n+1)) :=
    div_pos (mul_pos hK hB) (mul_pos hn' (g_pos _))
  refine ⟨ht,mul_nonneg ht.le (renewal_top_cost_nonneg n),?_⟩
  calc
    _ ≤ (K*B/((n:ℝ)*g (n+1)))*g (n+1) :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (a_pos (by omega)).le) ht.le
    _ = _ := by field_simp [(g_pos (n+1)).ne',hn'.ne']

lemma renewal_gap_cost_comparison {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hupper : ∀ n : ℕ,g n ≤ C*(rho^n)⁻¹) (n : ℕ) :
    (c*rho/C)*g (n+1) ≤ c*(rho^n)⁻¹ := by
  have hh := mul_le_mul_of_nonneg_left (hupper (n+1))
    (div_nonneg (mul_nonneg hc.le rho_pos.le) hC.le)
  apply hh.trans_eq
  rw [pow_succ]
  field_simp [rho_pos.ne',hC.ne']

end TotientAsymptotic

end

end OAI
