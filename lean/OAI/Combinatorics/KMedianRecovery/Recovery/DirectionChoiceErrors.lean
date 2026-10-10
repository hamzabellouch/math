import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.SetFunction

namespace OAI

namespace MetricKMedianRecovery
namespace Categorical
variable {E : Type*} [Fintype E] [DecidableEq E]

lemma direction_le_of_choiceErrors {err : ℝ} (b c : Batch E) (g : SetFunction E)
    (S : Finset E) (h : ChoiceErrors err b c g S) :
    direction c g S ≤ direction b g S + (b.length : ℝ) * err := by
  induction b generalizing c g with
  | nil => cases c with
    | nil => simp [direction]
    | cons p c => exact h.elim
  | cons p b ih =>
    cases c with
    | nil => exact h.elim
    | cons q c =>
      rcases p with ⟨w,e⟩
      rcases q with ⟨v,f⟩
      obtain ⟨hw, hs, hr⟩ := h
      subst v
      have hweights := choiceErrors_weights b c (operator w g) S hr
      have hhead := evaluate_eq_of_sameWeights b c hweights (marginal g f) S
      have ht := ih c (operator w g) hr
      simp only [direction, List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

lemma two_estimates_choice {trueChosen trueOther estChosen estOther tol : ℝ}
    (hchosen : |estChosen - trueChosen| ≤ tol)
    (hother : |estOther - trueOther| ≤ tol) (hmax : estOther ≤ estChosen) :
    trueOther ≤ trueChosen + 2 * tol := by
  rcases abs_le.mp hchosen with ⟨hca,hcb⟩
  rcases abs_le.mp hother with ⟨hoa,hob⟩
  linarith

theorem estimated_comparison_direction (b c : Batch E) (g : SetFunction E)
    (hb : ∀ p ∈ c, IsWeight p.1) (hmono : Monotone g) (hsub : Diminishing g)
    {err : ℝ} (S : Finset E) (h : ChoiceErrors err b c g S) :
    g (choices c) - evaluate b g S - (b.length : ℝ) * err ≤ direction b g S := by
  have hw := choiceErrors_weights b c g S h
  have hc := categorical_comparison_direction c g hb hmono hsub S
  rw [← evaluate_eq_of_sameWeights b c hw g S] at hc
  have hd := direction_le_of_choiceErrors b c g S h
  linarith

end Categorical

lemma affine_growth_bound (F : ℕ → ℝ) {r Q : ℝ} (n : ℕ)
    (_hr : 0 ≤ r) (hr1 : r ≤ 1) (h0 : 0 ≤ F 0)
    (hstep : ∀ t < n, (1-r) * F t + r * Q ≤ F (t+1)) :
    (1-(1-r)^n) * Q ≤ F n := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hi := ih (fun t ht => hstep t (Nat.lt_succ_of_lt ht))
    have hi' := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hr1)
    have hs := hstep n (Nat.lt_succ_self n)
    rw [pow_succ]
    nlinarith

lemma continuous_greedy_growth (F : ℕ → ℝ) (T : ℕ) (hT : 0 < T)
    {opt M tau : ℝ} (hM : 0 ≤ M) (hMo : M ≤ opt) (htau : 0 ≤ tau)
    (htau1 : tau ≤ 1/8) (h0 : 0 ≤ F 0)
    (hstep : ∀ t < T, F t + (opt - F t - 3*tau*M) / T ≤ F (t+1)) :
    (1 - 1 / Real.exp 1 - 3*tau) * opt ≤ F T := by
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hT1 : (1 : ℝ) ≤ T := Nat.one_le_cast.mpr hT
  have hopt : 0 ≤ opt := hM.trans hMo
  have hQ : 0 ≤ opt - 3*tau*M := by nlinarith
  have hi := affine_growth_bound F (r := 1/(T:ℝ)) (Q := opt-3*tau*M) T
    (by positivity) ((div_le_one hTR).mpr hT1) h0 (by
      intro t ht
      have hs := hstep t ht
      convert hs using 1; ring)
  have he := Real.one_sub_div_pow_le_exp_neg (n := T) (t := (1:ℝ)) hT1
  rw [Real.exp_neg] at he
  have he' := mul_le_mul_of_nonneg_right (sub_le_sub_left he 1) hQ
  have hexp : 0 ≤ 1 / Real.exp 1 := by positivity
  have hexp1 : 1 / Real.exp 1 ≤ 1 := by
    apply (div_le_one (Real.exp_pos _)).mpr
    exact Real.one_le_exp_iff.mpr (by norm_num)
  have hprod : (1 - 1 / Real.exp 1) * M ≤ opt := by nlinarith
  have hprod' := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 3*tau by positivity)
  calc
    (1 - 1 / Real.exp 1 - 3*tau) * opt ≤
        (1 - 1 / Real.exp 1) * (opt - 3*tau*M) := by nlinarith
    _ ≤ (1 - (1-1/(T:ℝ))^T) * (opt-3*tau*M) := by simpa only [one_div] using he'
    _ ≤ F T := hi

end MetricKMedianRecovery

end OAI
