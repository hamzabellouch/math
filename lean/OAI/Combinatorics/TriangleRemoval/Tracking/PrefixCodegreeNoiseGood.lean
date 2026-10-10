import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixCodegreeNoiseExit
import OAI.Combinatorics.TriangleRemoval.Tracking.RootedCompletionMax

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

def PrefixCodegreeNoiseGood (n : ℕ) (ω : History (Graph n) (prefixTime n)) : Prop :=
  ∀ u v : Fin n, ¬ PrefixCodegreeNoiseExit u v ω

theorem prefix_codegree_noise_failure : ∀ᶠ n : ℕ in atTop,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
      (fun ω => if PrefixCodegreeNoiseGood n ω then 0 else 1) ≤
      Real.exp (-2*(Real.log (n : ℝ))^(4/3 : ℝ)) := by
  filter_upwards [prefix_codegree_relative_noise_bound,codegree_noise_exponent_lower,
    prefixTemplateFactor_subpower 2 (by norm_num : (0 : ℝ) < 1/2500) (by norm_num : (0 : ℝ) < 1),
    polynomial_logsquare_le_prefix_margin 4 4,eventually_ge_atTop (1 : ℕ)] with n ht hexp hlog hb hn
  let μ := historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hr : 0 < codegreeNoiseRadius n := Real.rpow_pos_of_pos hn0 _
  have hexp' : (Real.log (n : ℝ))^2/4 ≤ codegreeNoiseRadius n^2/codegreeNoiseDenominator n := by
    have hh : (1+Real.log (n : ℝ))^2 ≤ (n : ℝ)^(1/2500 : ℝ) := by
      simpa only [prefixTemplateFactor,Real.rpow_two,one_mul] using hlog
    have hln := Real.log_nonneg hn1
    nlinarith only [hh,hln,hexp,sq_nonneg (Real.log (n : ℝ))]
  have hsingle (uv : Fin n × Fin n) :
      pmfMean μ (fun ω => if PrefixCodegreeNoiseExit uv.1 uv.2 ω then 1 else 0) ≤
      2*(prefixTime n+1 : ℝ)*Real.exp (-(Real.log (n : ℝ))^2/4) := by
    have ht' : pmfMean μ (fun ω => if PrefixCodegreeNoiseExit uv.1 uv.2 ω then 1 else 0) ≤
        2*(prefixTime n+1 : ℝ)*Real.exp (-(codegreeNoiseRadius n)^2/codegreeNoiseDenominator n) := by
      unfold codegreeNoiseDenominator
      refine le_trans ?_ (ht uv.1 uv.2 (codegreeNoiseRadius n) hr)
      apply le_of_eq
      congr 1
      funext ω
      by_cases hω : PrefixCodegreeNoiseExit uv.1 uv.2 ω <;>
        simp_all only [PrefixCodegreeNoiseExit, ite_true, ite_false]
    apply ht'.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    rw [neg_div,neg_div]
    exact neg_le_neg hexp'
  have hu := pmfMean_event_union μ Finset.univ (fun uv : Fin n × Fin n => PrefixCodegreeNoiseExit uv.1 uv.2)
  have hs : (∑ uv : Fin n × Fin n,
      pmfMean μ (fun ω => if PrefixCodegreeNoiseExit uv.1 uv.2 ω then 1 else 0)) ≤
      4*(n : ℝ)^4*Real.exp (-(Real.log (n : ℝ))^2/4) := by
    calc
      _ ≤ ∑ _uv : Fin n × Fin n, 2*(prefixTime n+1 : ℝ)*Real.exp (-(Real.log (n : ℝ))^2/4) :=
        Finset.sum_le_sum (fun uv _ => hsingle uv)
      _ = (n : ℝ)^2*(2*(prefixTime n+1))*Real.exp (-(Real.log (n : ℝ))^2/4) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have htime : (prefixTime n : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast prefixTime_le_square n
        have hnt : 1 ≤ (n : ℝ)^2 := by nlinarith
        nlinarith only [mul_le_mul_of_nonneg_left htime (sq_nonneg (n : ℝ)),
          mul_le_mul_of_nonneg_left hnt (sq_nonneg (n : ℝ))]
  rw [show (n : ℝ)^(4 : ℝ) = (n : ℝ)^4 from Real.rpow_natCast _ 4] at hb
  have hf := hu.trans (hs.trans hb)
  convert hf using 1
  apply congrArg (pmfMean μ)
  funext ω
  have he : (∃ uv ∈ (Finset.univ : Finset (Fin n × Fin n)), PrefixCodegreeNoiseExit uv.1 uv.2 ω) ↔
      ¬ PrefixCodegreeNoiseGood n ω := by simp [PrefixCodegreeNoiseGood,Prod.exists]
  simp only [he, ite_not]

end SharpTerminalLeave
end
end

end OAI
