import Mathlib
import OAI.Combinatorics.KMedian.Process.SurvivalProbability
import OAI.Combinatorics.KMedian.Sparse.SparsePhysicalBatch

namespace OAI

section
section
namespace MetricKMedian.SparsePhysicalBatch
open Finset
variable {n : ℕ}

theorem marginal_lower (Z : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {N : ℕ} (hq : ∀ e, (p:ℝ) ≤ q e) (hC : ∀ e, (C e).card ≤ N)
    (hself : ∀ e, e ∉ C e) (e : Fin n) :
    (p:ℝ)/2-(N:ℝ)*(p:ℝ)^2/2 ≤ (law Z C p q hp hq0).real.prob (fun A => e ∈ A) := by
  have hpR : (0:ℝ) ≤ p := by exact_mod_cast hp.1
  rw [marginal Z C p q hp hq0 e]
  by_cases he : e ∈ Z
  · rw [ite_eq_left he]
    have herror := SparseBernoulli.filtered_error p hp (by norm_num : 2 ≤ 4) C e (hself e)
    have hn := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hC e) : ((C e).card:ℝ) ≤ N)
      (sq_nonneg (p:ℝ))
    have hh := (abs_le.mp herror).1
    nlinarith only [hh, hn]
  · rw [ite_eq_right he]
    have hn : 0 ≤ (N:ℝ)*(p:ℝ)^2 := by positivity
    linarith only [hq e, hn]

theorem erasure_lower (Z R : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {N : ℕ} (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ 2*(p:ℝ)) (hC : ∀ e, (C e).card ≤ N)
    (hself : ∀ e, e ∉ C e) :
    (R.card:ℝ)*(p:ℝ)/2-(R.card:ℝ)*(N:ℝ)*(p:ℝ)^2/2-2*(R.card:ℝ)^2*(p:ℝ)^2 ≤
      (law Z C p q hp hq0).real.prob (fun A => ∃ e ∈ R, e ∈ A) := by
  have hpR : (0:ℝ) ≤ p := by exact_mod_cast hp.1
  let μ := (law Z C p q hp hq0).real
  have hfirst : (R.card:ℝ)*((p:ℝ)/2-(N:ℝ)*(p:ℝ)^2/2) ≤
      ∑ e : R, μ.prob (fun A => e.val ∈ A) := by
    have h := sum_le_sum (fun e (_ : e ∈ (univ : Finset R)) =>
      marginal_lower Z C p q hp hq0 (fun e => (hq e).1) hC hself e.val)
    simpa only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe] using h
  have hpair : ∀ e f : R, e ≠ f → μ.prob (fun A => e.val ∈ A ∧ f.val ∈ A) ≤ 4*(p:ℝ)^2 := by
    intro e f hef
    have h := pair_le Z C p q hp hq0 e.val f.val
      (show e.val ≠ f.val from fun h => hef (Subtype.ext h))
    have hm := mul_le_mul (hq e.val).2 (hq f.val).2 (show (0:ℝ) ≤ q f.val by exact_mod_cast (hq0 f.val).1) (by positivity : 0 ≤ 2*(p:ℝ))
    nlinarith only [h, hm, sq_nonneg (p:ℝ)]
  have hpairSum : (∑ ef ∈ (univ : Finset R).offDiag,
        μ.prob (fun A => ef.1.val ∈ A ∧ ef.2.val ∈ A)) ≤ 4*(R.card:ℝ)^2*(p:ℝ)^2 := by
    have h := sum_le_sum (fun ef (hef : ef ∈ (univ : Finset R).offDiag) =>
      hpair ef.1 ef.2 (mem_offDiag.mp hef).2.2)
    simp only [sum_const, nsmul_eq_mul] at h
    have hc : ((univ : Finset R).offDiag.card:ℝ) ≤ (R.card:ℝ)^2 := by
      have hn : (univ : Finset R).offDiag.card ≤ R.card*R.card := by
        rw [offDiag_card, card_univ, Fintype.card_coe]
        exact Nat.sub_le _ _
      exact_mod_cast (show (univ : Finset R).offDiag.card ≤ R.card^2 by simpa only [pow_two] using hn)
    have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 4*(p:ℝ)^2)
    nlinarith only [h, hm]
  have h := FiniteLaw.prob_exists_ge μ (fun e : R => fun A => e.val ∈ A)
  have heq : μ.prob (fun A => ∃ e : R, e.val ∈ A) = μ.prob (fun A => ∃ e ∈ R, e ∈ A) := by
    apply FiniteLaw.prob_congr
    intro A
    exact ⟨fun ⟨e, he⟩ => ⟨e.val, e.property, he⟩,
      fun ⟨e, he, ha⟩ => ⟨⟨e, he⟩, ha⟩⟩
  rw [heq] at h
  nlinarith only [h, hfirst, hpairSum]

theorem erasure_at_least_quarter (Z R : Finset (Fin n)) (C : Fin n → Finset (Fin n))
    (p : ℚ) (q : Fin n → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {N : ℕ} (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ 2*(p:ℝ)) (hC : ∀ e, (C e).card ≤ N)
    (hself : ∀ e, e ∉ C e) (hstep : (p:ℝ)*(2*(N:ℝ)+8*(R.card:ℝ)) ≤ 1) :
    (R.card:ℝ)*(p:ℝ)/4 ≤
      (law Z C p q hp hq0).real.prob (fun A => ∃ e ∈ R, e ∈ A) := by
  have hpR : (0:ℝ) ≤ p := by exact_mod_cast hp.1
  have h := erasure_lower Z R C p q hp hq0 hq hC hself
  have hm := mul_le_mul_of_nonneg_left hstep (by positivity : 0 ≤ (R.card:ℝ)*(p:ℝ))
  nlinarith only [h, hm]

end MetricKMedian.SparsePhysicalBatch
end
end

end OAI
