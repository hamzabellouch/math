import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixTimeSquare
import OAI.Combinatorics.TriangleRemoval.Tracking.CodegreeVertexCount
import OAI.Combinatorics.TriangleRemoval.Tracking.CodegreeNoiseRadius

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

def PrefixCodegreeNoiseExit {n : ℕ} (u v : Fin n)
    (ω : History (Graph n) (prefixTime n)) : Prop :=
  ∃ j ≤ prefixTime n,
    (∀ k < j, (currentCodegree (ω (historyIndex (prefixTime n) k)) u v : ℝ) ≤
      2*earlyTemplateScale 1 2 n k) ∧
    codegreeNoiseRadius n ≤ |historyNoise (fun _ => step)
      (fun k H => (currentCodegree H u v : ℝ)/earlyTemplateScale 1 2 n k)
      (prefixTime n) j ω|

open Classical in

theorem all_codegree_stopped_noise_envelope : ∀ᶠ n : ℕ in atTop,
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step)
      (prefixTime n) (prefixTime n))
      (fun ω => if ∃ uv : Fin n × Fin n, PrefixCodegreeNoiseExit uv.1 uv.2 ω
        then 1 else 0) ≤ Real.exp (-(Real.log n)^(4/3 : ℝ)) := by
  filter_upwards [prefix_codegree_relative_noise_bound,codegree_noise_exponent_lower,
    polynomial_exponential_le_prefix_envelope 4 4 (1/2500) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n htail hexp hbudget hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hr : 0 < codegreeNoiseRadius n := Real.rpow_pos_of_pos hn0 _
  have hh := pmfMean_event_union
    (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n))
    (Finset.univ : Finset (Fin n × Fin n))
    (fun uv ω => PrefixCodegreeNoiseExit uv.1 uv.2 ω)
  simp only [Finset.mem_univ,true_and] at hh
  apply hh.trans
  calc
    _ ≤ ∑ _uv : Fin n × Fin n, 2*(prefixTime n+1 : ℝ)*Real.exp (-(n : ℝ)^(1/2500 : ℝ)) := by
      apply Finset.sum_le_sum
      intro uv _
      have ht := htail uv.1 uv.2 (codegreeNoiseRadius n) hr
      have ht' : pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step)
          (prefixTime n) (prefixTime n))
          (fun ω => if PrefixCodegreeNoiseExit uv.1 uv.2 ω then 1 else 0) ≤
          2*(prefixTime n+1 : ℝ)*Real.exp
            (-(codegreeNoiseRadius n)^2/codegreeNoiseDenominator n) := by
        unfold codegreeNoiseDenominator
        refine le_trans ?_ ht
        apply le_of_eq
        congr 1
        funext ω
        by_cases hω : PrefixCodegreeNoiseExit uv.1 uv.2 ω <;>
          simp_all only [PrefixCodegreeNoiseExit, ite_true, ite_false]
      apply ht'.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      exact neg_le_neg hexp
    _ = (n : ℝ)^2*2*(prefixTime n+1)*Real.exp (-(n : ℝ)^(1/2500 : ℝ)) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_mul]
      ring
    _ ≤ 4*(n : ℝ)^4*Real.exp (-(n : ℝ)^(1/2500 : ℝ)) := by
      have ht : (prefixTime n : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast prefixTime_le_square n
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hn2 : (1 : ℝ) ≤ (n : ℝ)^2 := one_le_pow₀ hn1
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      nlinarith [sq_nonneg (n : ℝ)]
    _ ≤ _ := by
      rw [show (n : ℝ)^(4 : ℝ) = (n : ℝ)^4 from Real.rpow_natCast _ 4] at hbudget
      exact hbudget

end SharpTerminalLeave

end

end OAI
