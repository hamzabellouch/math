import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.LogCorrelation
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Tent

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset

namespace OrdinaryLogIntegral
open Finset

lemma weighted_partial_sum_bound (w : ℕ → ℝ) (z : ℕ → ℂ) (N : ℕ)
    {S V W : ℝ} (hS : 0 ≤ S) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hw : |w (N-1)| ≤ W)
    (hvar : ∀ n < N-1, |w (n+1)-w n| ≤ V)
    (hz : ∀ n ≤ N, ‖∑ k ∈ range n, z k‖ ≤ S) :
    ‖∑ n ∈ range N, (w n : ℂ)*z n‖ ≤ (W+(N : ℝ)*V)*S := by
  have he := sum_range_by_parts w z N
  simp only [Complex.real_smul] at he
  rw [he]
  calc
    _ ≤ ‖(w (N-1) : ℂ)*(∑ k ∈ range N, z k)‖ +
        ‖∑ n ∈ range (N-1), ((w (n+1)-w n : ℝ) : ℂ)*(∑ k ∈ range (n+1), z k)‖ := norm_sub_le _ _
    _ ≤ W*S + ∑ n ∈ range (N-1), V*S := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hw (hz N le_rfl) (norm_nonneg _) hW
      · apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro n hn
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hvar n (mem_range.mp hn)) (hz (n+1) (by have := mem_range.mp hn; omega)) (norm_nonneg _) hV
    _ ≤ (W+(N : ℝ)*V)*S := by
      simp only [sum_const, card_range, nsmul_eq_mul]
      have hNN : ((N-1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
      nlinarith [mul_le_mul_of_nonneg_right hNN (mul_nonneg hV hS)]

lemma logPhase_mul (t : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    logPhase t (x*y) = logPhase t x * logPhase t y := by
  simp only [logPhase, Real.log_mul (ne_of_gt hx) (ne_of_gt hy), ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma tentPhase_eq (t a H x : ℝ) (hH : 0 < H) :
    tentPhase t a H x = (tent a H x : ℂ)*logPhase t x := by
  by_cases hx : a ≤ x
  · simp only [tentPhase, max_eq_right hx]
  · rw [tentPhase_zero_left t a H x hH (le_of_not_ge hx), tent_zero_left a H x hH (le_of_not_ge hx)]
    simp

lemma weighted_logPhase_bound (t a H d b : ℝ) (N : ℕ) (hH : 0 < H)
    (hd : 0 < d) (hb : 0 < b) {S : ℝ} (hS : 0 ≤ S)
    (hsum : ∀ n ≤ N, ‖∑ k ∈ range n, logPhase t (b+k)‖ ≤ S) :
    ‖∑ n ∈ range N, tentPhase t a H (d*(b+n))‖ ≤ (1+(N : ℝ)*d/H)*S := by
  have he : (∑ n ∈ range N, tentPhase t a H (d*(b+n))) =
      logPhase t d * ∑ n ∈ range N, (tent a H (d*(b+n)) : ℂ)*logPhase t (b+n) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    rw [tentPhase_eq t a H _ hH, logPhase_mul t hd (by positivity)]
    ring
  rw [he, norm_mul, norm_logPhase, one_mul]
  have hh := weighted_partial_sum_bound (fun n => tent a H (d*(b+n)))
    (fun n => logPhase t (b+n)) N hS (div_nonneg hd.le hH.le) (show (0 : ℝ) ≤ 1 by norm_num)
    (by rw [abs_of_nonneg (tent_nonneg _ _ _)]; exact tent_le_one _ _ _ hH)
    (fun n hn => by
      have hl := tent_lipschitz a H (d*(b+(n+1 : ℕ))) (d*(b+n)) hH
      have he : d*(b+(n+1 : ℕ)) - d*(b+n) = d := by push_cast; ring
      rwa [he, abs_of_pos hd] at hl)
    hsum
  simpa only [div_eq_mul_inv, mul_assoc] using hh

noncomputable def differencingBudget (t a : ℝ) (N K : ℕ) : ℝ :=
  2*N*((K : ℝ)*N + 2*K*((7*(a+N+K)^2/|t|)*(∑ d ∈ Icc 1 K, (d : ℝ)⁻¹) +
    ((N : ℝ)*|t|/a^2)*(K : ℝ)^2)) + 8*(K : ℝ)^4

lemma differencingBudget_nonneg (t a : ℝ) (N K : ℕ) : 0 ≤ differencingBudget t a N K := by
  unfold differencingBudget
  positivity

lemma differencingBudget_mono (t a : ℝ) (N M K : ℕ) (ha : 0 ≤ a) (hNM : N ≤ M) :
    differencingBudget t a N K ≤ differencingBudget t a M K := by
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  unfold differencingBudget
  gcongr

lemma partial_logphase_bound (t a : ℝ) (N K : ℕ) (ha : 0 < a) (ht : t ≠ 0) (hK : 0 < K) :
    ∀ n ≤ N, ‖∑ k ∈ range n, logPhase t (a+k)‖ ≤
      Real.sqrt (differencingBudget t a N K)/(K : ℝ) := by
  intro n hn
  have hh := (discrete_logphase_bound t a n K ha ht).trans (differencingBudget_mono t a n N K ha.le hn)
  have hs := Real.sq_sqrt (differencingBudget_nonneg t a N K)
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  apply (le_div_iff₀ hk).mpr
  nlinarith [Real.sqrt_nonneg (differencingBudget t a N K), norm_nonneg (∑ k ∈ range n, logPhase t (a+k))]

theorem weighted_discrete_logphase (t a H d b : ℝ) (N K : ℕ)
    (hH : 0 < H) (hd : 0 < d) (hb : 0 < b) (ht : t ≠ 0) (hK : 0 < K) :
    ‖∑ n ∈ range N, tentPhase t a H (d*(b+n))‖ ≤
      (1+(N : ℝ)*d/H)*(Real.sqrt (differencingBudget t b N K)/(K : ℝ)) := by
  exact weighted_logPhase_bound t a H d b N hH hd hb (by positivity)
    (partial_logphase_bound t b N K hb ht hK)

end OrdinaryLogIntegral

end

end OAI
