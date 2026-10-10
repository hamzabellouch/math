import OAI.NumberTheory.TwoPoint.Bounds.MultiplicativePrimeProducts
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.PSeries

namespace OAI

/-! A fixed finite exclusion set makes all later finite prime costs small. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma summable_prime_cost_tail (r : ℕ → ℝ)
    (hr : ∀ p, p.Prime → 0 ≤ r p)
    (hs : Summable (fun p : ℕ => if p.Prime then r p else 0))
    (E₀ : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ E : Finset ℕ, E₀ ⊆ E ∧ ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → Disjoint P E → (∑ p ∈ P, r p) < ε := by
  obtain ⟨S, hS⟩ := summable_iff_vanishing_norm.mp hs ε hε
  refine ⟨E₀ ∪ S, subset_union_left, ?_⟩
  intro P hP hdis
  have hd : Disjoint P S := hdis.mono_right subset_union_right
  have hh := hS P hd
  have he : (∑ p ∈ P, if p.Prime then r p else 0) = ∑ p ∈ P, r p := by
    apply sum_congr rfl
    intro p hp
    rw [ite_eq_left (hP p hp)]
  rw [he, Real.norm_eq_abs, abs_of_nonneg (sum_nonneg (fun p hp => hr p (hP p hp)))] at hh
  exact hh

lemma pair_prime_defect_summable {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g)
    (hsf : Summable (fun p : ℕ => if p.Prime then (1 - ‖f p‖) / (p : ℝ) else 0))
    (hsg : Summable (fun p : ℕ => if p.Prime then (1 - ‖g p‖) / (p : ℝ) else 0)) :
    Summable (fun p : ℕ => if p.Prime then (1 - ‖f p * g p‖) / (p : ℝ) else 0) := by
  apply Summable.of_nonneg_of_le _ _ (hsf.add hsg)
  · intro p
    split_ifs with hp
    · apply div_nonneg _ (Nat.cast_nonneg p)
      rw [norm_mul]
      exact sub_nonneg.mpr ((mul_le_mul (hf p hp.pos) (hg p hp.pos)
        (norm_nonneg _) zero_le_one).trans (by norm_num))
    · exact le_rfl
  · intro p
    by_cases hp : p.Prime
    · simp only [hp, ite_true]
      rw [← add_div]
      exact div_le_div_of_nonneg_right (prime_product_pair_defect hf hg p hp.pos)
        (Nat.cast_nonneg p)
    · simp only [hp, ite_false, add_zero, le_refl]

lemma exists_prime_defect_exclusion {f g : ℕ → ℂ}
    (hf : OneBounded f) (hg : OneBounded g)
    (hsf : Summable (fun p : ℕ => if p.Prime then (1 - ‖f p‖) / (p : ℝ) else 0))
    (hsg : Summable (fun p : ℕ => if p.Prime then (1 - ‖g p‖) / (p : ℝ) else 0))
    (E₀ : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ E : Finset ℕ, E₀ ⊆ E ∧ ∀ P : Finset ℕ,
      (∀ p ∈ P, p.Prime) → Disjoint P E →
      (∑ p ∈ P, (1 - ‖f p * g p‖) / (p : ℝ)) < ε ∧
        (∑ p ∈ P, 1 / (p : ℝ) ^ 2) < ε := by
  have hd := pair_prime_defect_summable hf hg hsf hsg
  have hsq : Summable (fun p : ℕ => if p.Prime then 1 / (p : ℝ) ^ 2 else 0) := by
    apply Summable.of_nonneg_of_le (fun p => by positivity) _
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
    intro p
    split_ifs <;> first | exact le_rfl | positivity
  obtain ⟨E₁, hE₁, htail₁⟩ := summable_prime_cost_tail
    (fun p => (1 - ‖f p * g p‖) / (p : ℝ)) (fun p hp => by
      apply div_nonneg _ (Nat.cast_nonneg p)
      rw [norm_mul]
      exact sub_nonneg.mpr ((mul_le_mul (hf p hp.pos) (hg p hp.pos)
        (norm_nonneg _) zero_le_one).trans (by norm_num))) hd E₀ ε hε
  obtain ⟨E₂, hE₂, htail₂⟩ := summable_prime_cost_tail
    (fun p => 1 / (p : ℝ) ^ 2) (fun p _ => by positivity) hsq E₁ ε hε
  refine ⟨E₂, hE₁.trans hE₂, ?_⟩
  intro P hP hPE
  exact ⟨htail₁ P hP (hPE.mono_right hE₂), htail₂ P hP hPE⟩

end TwoPointCorrelations

end OAI
