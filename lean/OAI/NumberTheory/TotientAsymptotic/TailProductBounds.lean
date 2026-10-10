import OAI.NumberTheory.TotientAsymptotic.HeadLimitedPrimeMass

namespace OAI

/-! The capped tail has the subpower denominator required by the prime window. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma prime_tail_log_bound {n : ℕ} (p : Fin n → ℕ)
    (hp : ∀ i,(p i).Prime) {T : ℝ} (hT : ∀ i,primePrefixCoord p i ≤ T) :
    Real.log ((∏ i,p i : ℕ):ℝ) ≤ n*Real.exp T := by
  rw [Nat.cast_prod,Real.log_prod (fun i _ => by exact_mod_cast (hp i).ne_zero)]
  calc
    _ ≤ ∑ i : Fin n,Real.exp T := by
      apply Finset.sum_le_sum
      intro i _
      have hi := Real.exp_le_exp.mpr (hT i)
      have hip : (1:ℝ) < p i := by exact_mod_cast (hp i).one_lt
      simpa only [primePrefixCoord,Real.exp_log (Real.log_pos hip)] using hi
    _ = _ := by simp

lemma capped_tail_denominator_budget (d : ℕ) : ∀ᶠ x : ℝ in atTop,
    Real.log (d:ℝ)+(m x:ℝ)*Real.exp ((19/25:ℝ)*B x) ≤ (Real.log x)^(4/5:ℝ) := by
  have h₁ : Tendsto (fun x : ℝ => B x*Real.exp (-(1/25:ℝ)*B x)) atTop (nhds 0) := by
    simpa only [Real.rpow_one,Function.comp_def,neg_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (1/25) (by norm_num)).comp B_tendsto
  have h₂ : Tendsto (fun x : ℝ => Real.log (d:ℝ)*Real.exp (-(4/5:ℝ)*B x)) atTop (nhds 0) := by
    simpa only [Real.rpow_zero,one_mul,mul_zero,Function.comp_def,neg_mul] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) (4/5) (by norm_num)).comp B_tendsto).const_mul (Real.log (d:ℝ))
  have hs := (h₁.add h₂).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)+0<1))
  filter_upwards [hs,ambient_polynomial_budget 1 1,eventually_gt_atTop (1:ℝ)] with x hx hm hx1
  have hm' : (m x:ℝ) ≤ B x := by simpa only [one_mul,pow_one] using hm
  have he : (B x*Real.exp (-(1/25:ℝ)*B x)+Real.log (d:ℝ)*Real.exp (-(4/5:ℝ)*B x))*
      Real.exp ((4/5:ℝ)*B x)=
      B x*Real.exp ((19/25:ℝ)*B x)+Real.log (d:ℝ) := by
    rw [add_mul,mul_assoc,mul_assoc,←Real.exp_add,←Real.exp_add]
    rw [show -(1/25:ℝ)*B x+(4/5:ℝ)*B x=(19/25:ℝ)*B x by ring,
      show -(4/5:ℝ)*B x+(4/5:ℝ)*B x=0 by ring,Real.exp_zero,mul_one]
  have hh := mul_le_mul_of_nonneg_right hx.le (Real.exp_pos ((4/5:ℝ)*B x)).le
  rw [he,one_mul] at hh
  have hpower : Real.exp ((4/5:ℝ)*B x)=(Real.log x)^(4/5:ℝ) := by
    rw [Real.rpow_def_of_pos (Real.log_pos hx1)]
    unfold B
    rw [mul_comm]
  rw [hpower] at hh
  have hmul := mul_le_mul_of_nonneg_right hm' (Real.exp_pos ((19/25:ℝ)*B x)).le
  linarith only [hmul,hh]

lemma capped_prime_tail_denominator {d : ℕ} (hd : 0 < d) :
    ∀ᶠ x : ℝ in atTop,∀ n : ℕ,n ≤ m x → ∀ p : Fin n → ℕ,
      (∀ i,(p i).Prime) → (∀ i,primePrefixCoord p i ≤ (19/25:ℝ)*B x) →
      Real.log ((d*(∏ i,p i).totient:ℕ):ℝ) ≤ (Real.log x)^(4/5:ℝ) := by
  filter_upwards [capped_tail_denominator_budget d] with x hx
  intro n hn p hp hcap
  have hr : 0 < ∏ i,p i := Finset.prod_pos (fun i _ => (hp i).pos)
  have hφ : 0 < (∏ i,p i).totient := Nat.totient_pos.mpr hr
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hφ' : (0:ℝ) < (∏ i,p i:ℕ).totient := by exact_mod_cast hφ
  have hlog := Real.log_le_log hφ'
    (show ((∏ i,p i:ℕ).totient:ℝ) ≤ (∏ i,p i:ℕ) by
      exact_mod_cast Nat.totient_le (∏ i,p i))
  have htail := prime_tail_log_bound p hp hcap
  have hdim := mul_le_mul_of_nonneg_right (show (n:ℝ) ≤ m x by exact_mod_cast hn)
    (Real.exp_pos ((19/25:ℝ)*B x)).le
  rw [Nat.cast_mul,Real.log_mul hd'.ne' hφ'.ne']
  linarith only [hlog,htail,hdim,hx]

end TotientAsymptotic

end

end OAI
