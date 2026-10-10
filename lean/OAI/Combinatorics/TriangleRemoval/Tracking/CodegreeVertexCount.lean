import Mathlib
import OAI.Combinatorics.TriangleRemoval.Asymptotics.EarlyDensity
import OAI.Combinatorics.TriangleRemoval.Tracking.CodegreeRelativeNoiseTail

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

lemma codegree_le_vertex_count {n : ℕ} (G : Graph n) (u v : Fin n) :
    currentCodegree G u v ≤ n := by
  unfold currentCodegree
  exact (Finset.card_le_univ _).trans (by simp)

lemma earlyCodegreeScale_ge_prefixD (n i : ℕ) (hi : i ≤ prefixTime n)
    (hp : 0 ≤ prefixDensity n) : prefixD n ≤ earlyTemplateScale 1 2 n i := by
  unfold earlyTemplateScale prefixD
  rw [pow_one]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hp (earlyDensity_antitone n hi) 2) (Nat.cast_nonneg n)

lemma initial_codegree_relative_le_four {n : ℕ} (hn : 2 ≤ n) (u v : Fin n) :
    (currentCodegree (completeGraph n) u v : ℝ)/earlyTemplateScale 1 2 n 0 ≤ 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (1/2 : ℝ) ≤ earlyDensity n 0 := by
    have hh : 1/(n : ℝ) ≤ 1/2 := (div_le_iff₀ hn0).mpr (by linarith)
    simp only [earlyDensity,Nat.cast_zero,mul_zero,zero_div,sub_zero]
    linarith
  have hs : (n : ℝ)/4 ≤ earlyTemplateScale 1 2 n 0 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hp 2)
      hn0.le
    unfold earlyTemplateScale
    norm_num only [pow_one,div_pow,one_pow] at hh ⊢
    nlinarith only [hh]
  apply (div_le_iff₀ (lt_of_lt_of_le (by positivity) hs)).mpr
  have hh : (currentCodegree (completeGraph n) u v : ℝ) ≤ n := by
    exact_mod_cast codegree_le_vertex_count (completeGraph n) u v
  linarith

open Classical in

theorem prefix_codegree_relative_noise_bound : ∀ᶠ n : ℕ in atTop,
    ∀ u v : Fin n, ∀ r : ℝ, 0 < r →
    pmfMean (historyLaw (PMF.pure (completeGraph n)) (fun _ => step)
      (prefixTime n) (prefixTime n))
      (fun ω => if ∃ j ≤ prefixTime n,
        (∀ k < j, (currentCodegree (ω (historyIndex (prefixTime n) k)) u v : ℝ) ≤
          2*earlyTemplateScale 1 2 n k) ∧
        r ≤ |historyNoise (fun _ => step)
          (fun k H => (currentCodegree H u v : ℝ)/earlyTemplateScale 1 2 n k)
          (prefixTime n) j ω| then 1 else 0) ≤
      2*(prefixTime n+1 : ℝ)*Real.exp
        (-r^2/(4*((6/prefixD n)*(4+8*Real.log n+r+6/prefixD n)+(6/prefixD n)*r))) := by
  filter_upwards [earlyTemplateScale_regular 1 2,earlyTemplateScale_log_budget 1 2,
    prefixDensity_eventually_inverse_lower,eventually_ge_atTop (2 : ℕ)] with n hreg hbudget hp hn
  intro u v r hr
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpp : 0 < prefixDensity n := lt_of_lt_of_le (by positivity) hp
  have hD : 0 < prefixD n := by unfold prefixD; positivity
  have hc : 0 < 6/prefixD n := by positivity
  have hjump : ∀ k < prefixTime n, 6/earlyTemplateScale 1 2 n (k+1) ≤ 6/prefixD n := by
    intro k hk
    exact div_le_div_of_nonneg_left (by norm_num) hD
      (earlyCodegreeScale_ge_prefixD n (k+1) (by omega) hpp.le)
  have ht := codegree_relative_noise_tail u v (completeGraph n) (prefixTime n)
    (earlyTemplateScale 1 2 n) (6/prefixD n) 2 hc (by norm_num)
    hreg.1 hreg.2.1 hjump r hr
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  rw [neg_div,neg_div]
  apply neg_le_neg
  have hinit := initial_codegree_relative_le_four hn u v
  have hz := relativeScaleBudget_nonneg (earlyTemplateScale 1 2 n) (prefixTime n)
    hreg.1 hreg.2.1
  have hi0 : 0 ≤ (currentCodegree (completeGraph n) u v : ℝ)/earlyTemplateScale 1 2 n 0 :=
    div_nonneg (Nat.cast_nonneg _) (hreg.1 0 (Nat.zero_le _)).le
  have hd0 : 0 < 4*((6/prefixD n)*
      ((currentCodegree (completeGraph n) u v : ℝ)/earlyTemplateScale 1 2 n 0+
        2*relativeScaleBudget (earlyTemplateScale 1 2 n) (prefixTime n)+r+6/prefixD n)+
        (6/prefixD n)*r) := by positivity
  apply div_le_div_of_nonneg_left (sq_nonneg r) hd0
  have hh := mul_le_mul_of_nonneg_left (show
      (currentCodegree (completeGraph n) u v : ℝ)/earlyTemplateScale 1 2 n 0+
        2*relativeScaleBudget (earlyTemplateScale 1 2 n) (prefixTime n)+r+6/prefixD n ≤
        4+8*Real.log n+r+6/prefixD n by norm_num at hbudget; linarith)
    hc.le
  linarith

end SharpTerminalLeave

end

end OAI
