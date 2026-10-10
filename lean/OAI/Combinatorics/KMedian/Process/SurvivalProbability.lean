import Mathlib
import OAI.Combinatorics.KMedian.Process.PhysicalBatchLaw

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset

theorem prob_nonempty_ge {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (A : Ω → Finset E) :
    (∑ e, μ.prob (fun ω => e ∈ A ω)) -
      (1/2)*∑ p ∈ (univ : Finset E).offDiag,
        μ.prob (fun ω => p.1 ∈ A ω ∧ p.2 ∈ A ω) ≤
      μ.prob (fun ω => (A ω).Nonempty) := by
  have hpoint : ∀ ω, ((A ω).card:ℝ)-(1/2)*((A ω).offDiag.card:ℝ) ≤
      if (A ω).Nonempty then (1:ℝ) else 0 := by
    intro ω
    by_cases ha : (A ω).Nonempty
    · rw [ite_eq_left ha]
      have hn : 1 ≤ (A ω).card := card_pos.mpr ha
      have hcard : ((A ω).offDiag.card:ℝ) = ((A ω).card:ℝ)*(((A ω).card:ℝ)-1) := by
        rw [offDiag_card, show (A ω).card*(A ω).card-(A ω).card =
          (A ω).card*((A ω).card-1) by simp only [Nat.mul_sub_left_distrib, mul_one]]
        rw [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one]
      rw [hcard]
      rcases eq_or_lt_of_le hn with h | h
      · have hc : ((A ω).card:ℝ)=1 := by exact_mod_cast h.symm
        rw [hc]; norm_num
      · have hc : (2:ℝ) ≤ (A ω).card := by exact_mod_cast h
        nlinarith only [hc, sq_nonneg (((A ω).card:ℝ)-2)]
    · have he := not_nonempty_iff_eq_empty.mp ha
      simp only [he, card_empty, offDiag_empty, Nat.cast_zero, mul_zero,
        sub_zero, Finset.not_nonempty_empty, ite_false, le_refl]
  have h := μ.expect_mono hpoint
  have hcard : μ.expect (fun ω => ((A ω).card:ℝ)) =
      ∑ e, μ.prob (fun ω => e ∈ A ω) := by
    have hc := BatchRemainder.expect_selected_sum μ A (fun _ => (1:ℝ))
    simpa only [sum_const, nsmul_eq_mul, mul_one] using hc
  simpa only [expect_sub, expect_mul, hcard, BatchRemainder.expect_pair_count, prob] using h

theorem prob_exists_ge {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E]
    (μ : FiniteLaw Ω) (P : E → Ω → Prop) [∀ e, DecidablePred (P e)] :
    (∑ e, μ.prob (P e)) -
      (1/2)*∑ p ∈ (univ : Finset E).offDiag,
        μ.prob (fun ω => P p.1 ω ∧ P p.2 ω) ≤
      μ.prob (fun ω => ∃ e, P e ω) := by
  classical
  have h := prob_nonempty_ge μ (fun ω => univ.filter (fun e => P e ω))
  simpa only [mem_filter, mem_univ, true_and, filter_nonempty_iff,
    exists_prop, true_and] using h

end MetricKMedian.FiniteLaw

namespace MetricKMedian.PhysicalBatchLaw
open Finset
variable {E : Type*} [Fintype E] [DecidableEq E]

theorem marginal_lower (Z : Finset E) (C : E → Finset E)
    (p : ℝ) (q : E → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    {N : ℕ} (hq : ∀ e, p ≤ q e) (hC : ∀ e, (C e).card ≤ N)
    (hself : ∀ e, e ∉ C e) (e : E) :
    p/2-(N:ℝ)*p^2/2 ≤ (law Z C p q hp0 hp1 hq0 hq1).prob (fun A => e ∈ A) := by
  rw [marginal Z C p q hp0 hp1 hq0 hq1 e (hself e)]
  by_cases he : e ∈ Z
  · rw [ite_eq_left he]
    have herror := FiniteLaw.filtered_marginal_error p hp0 hp1 C e (hself e)
    rw [FiniteLaw.filtered_marginal p hp0 hp1 C e (hself e)] at herror
    have hn := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hC e) : ((C e).card:ℝ) ≤ N)
      (sq_nonneg p)
    have hh := (abs_le.mp herror).1
    nlinarith only [hh, hn]
  · rw [ite_eq_right he]
    have hn : 0 ≤ (N:ℝ)*p^2 := by positivity
    linarith only [hq e, hn]

theorem erasure_lower (Z R : Finset E) (C : E → Finset E)
    (p : ℝ) (q : E → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    {N : ℕ} (hq : ∀ e, p ≤ q e ∧ q e ≤ 2*p) (hC : ∀ e, (C e).card ≤ N)
    (hself : ∀ e, e ∉ C e) :
    (R.card:ℝ)*p/2-(R.card:ℝ)*(N:ℝ)*p^2/2-2*(R.card:ℝ)^2*p^2 ≤
      (law Z C p q hp0 hp1 hq0 hq1).prob (fun A => ∃ e ∈ R, e ∈ A) := by
  let μ := law Z C p q hp0 hp1 hq0 hq1
  have hfirst : (R.card:ℝ)*(p/2-(N:ℝ)*p^2/2) ≤
      ∑ e : R, μ.prob (fun A => e.val ∈ A) := by
    have h := sum_le_sum (fun e (_ : e ∈ (univ : Finset R)) =>
      marginal_lower Z C p q hp0 hp1 hq0 hq1 (fun e => (hq e).1) hC hself e.val)
    simpa only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe] using h
  have hpair : ∀ e f : R, e ≠ f → μ.prob (fun A => e.val ∈ A ∧ f.val ∈ A) ≤ 4*p^2 := by
    intro e f hef
    have h := pair_le Z C p q hp0 hp1 hq0 hq1
      (show e.val ≠ f.val from fun h => hef (Subtype.ext h))
    have hm := mul_le_mul (hq e.val).2 (hq f.val).2 (hq0 f.val) (by positivity : 0 ≤ 2*p)
    nlinarith only [h, hm, sq_nonneg p]
  have hpairSum : (∑ ef ∈ (univ : Finset R).offDiag,
        μ.prob (fun A => ef.1.val ∈ A ∧ ef.2.val ∈ A)) ≤ 4*(R.card:ℝ)^2*p^2 := by
    have h := sum_le_sum (fun ef (hef : ef ∈ (univ : Finset R).offDiag) =>
      hpair ef.1 ef.2 (mem_offDiag.mp hef).2.2)
    simp only [sum_const, nsmul_eq_mul] at h
    have hc : ((univ : Finset R).offDiag.card:ℝ) ≤ (R.card:ℝ)^2 := by
      have hn : (univ : Finset R).offDiag.card ≤ R.card*R.card := by
        rw [offDiag_card, card_univ, Fintype.card_coe]
        exact Nat.sub_le _ _
      exact_mod_cast (show (univ : Finset R).offDiag.card ≤ R.card^2 by simpa only [pow_two] using hn)
    have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 4*p^2)
    nlinarith only [h, hm]
  have h := FiniteLaw.prob_exists_ge μ (fun e : R => fun A => e.val ∈ A)
  have heq : μ.prob (fun A => ∃ e : R, e.val ∈ A) = μ.prob (fun A => ∃ e ∈ R, e ∈ A) := by
    apply FiniteLaw.prob_congr
    intro A
    exact ⟨fun ⟨e, he⟩ => ⟨e.val, e.property, he⟩,
      fun ⟨e, he, ha⟩ => ⟨⟨e, he⟩, ha⟩⟩
  rw [heq] at h
  nlinarith only [h, hfirst, hpairSum]

theorem erasure_at_least_quarter (Z R : Finset E) (C : E → Finset E)
    (p : ℝ) (q : E → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    {N : ℕ} (hq : ∀ e, p ≤ q e ∧ q e ≤ 2*p) (hC : ∀ e, (C e).card ≤ N)
    (hself : ∀ e, e ∉ C e) (hstep : p*(2*(N:ℝ)+8*(R.card:ℝ)) ≤ 1) :
    (R.card:ℝ)*p/4 ≤
      (law Z C p q hp0 hp1 hq0 hq1).prob (fun A => ∃ e ∈ R, e ∈ A) := by
  have h := erasure_lower Z R C p q hp0 hp1 hq0 hq1 hq hC hself
  have hm := mul_le_mul_of_nonneg_left hstep (by positivity : 0 ≤ (R.card:ℝ)*p)
  nlinarith only [h, hm]

end MetricKMedian.PhysicalBatchLaw
end
end

end OAI
