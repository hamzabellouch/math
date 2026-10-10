import OAI.NumberTheory.Ostmann.Supply.CompletionWeights

namespace OAI

noncomputable section
namespace Ostmann.Supply.CompletionCounting
open Finset

def squarefreeUpTo (R : ℕ) : Finset ℕ := (Icc 1 R).filter Squarefree

theorem primesUpTo_mono {U R : ℕ} (h : U ≤ R) : primesUpTo U ⊆ primesUpTo R := by
  intro p hp
  obtain ⟨hp, hprime⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hp).1, (mem_Icc.mp hp).2.trans h⟩, hprime⟩

theorem sum_completion_pairs_le (R : ℕ) (T : Finset ℕ) (b κ : ℕ → ℝ)
    (hb : ∀ t, 0 ≤ b t) (hκ : ∀ p, 0 ≤ κ p)
    (hT : ∀ t ∈ T, Squarefree t) :
    (∑ t ∈ T, (t : ℝ) * b t *
      ∑ u ∈ completions (R / t) t, primeProduct κ u) ≤
    ∑ q ∈ squarefreeUpTo R, ∑ t ∈ q.divisors,
      (t : ℝ) * b t * primeProduct κ (q / t) := by
  have hnonneg (t q : ℕ) : 0 ≤ (t : ℝ) * b t * primeProduct κ (q/t) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hb _)) (prod_nonneg fun p hp => hκ p)
  have hsingle (t : ℕ) (ht : t ∈ T) :
      (t : ℝ) * b t * (∑ u ∈ completions (R/t) t, primeProduct κ u) ≤
      ∑ q ∈ (squarefreeUpTo R).filter (t ∣ ·), (t : ℝ) * b t * primeProduct κ (q/t) := by
    have ht0 : 0 < t := (hT t ht).ne_zero.bot_lt
    have hsub : (completions (R/t) t).image (fun u => t*u) ⊆
        (squarefreeUpTo R).filter (t ∣ ·) := by
      intro q hq
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hq
      obtain ⟨hur, hsu, hcu⟩ := mem_filter.mp hu
      have hu0 : 0 < u := by have := (mem_Icc.mp hur).1; omega
      have hub : u*t ≤ R := (Nat.le_div_iff_mul_le ht0).mp (mem_Icc.mp hur).2
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (mul_ne_zero ht0.ne' hu0.ne'), by simpa [mul_comm] using hub⟩,
        (Nat.squarefree_mul hcu.symm).mpr ⟨hT t ht, hsu⟩⟩, dvd_mul_right t u⟩
    calc
      _ = ∑ q ∈ (completions (R/t) t).image (fun u => t*u),
          (t : ℝ) * b t * primeProduct κ (q/t) := by
        rw [sum_image (fun u hu v hv huv => Nat.eq_of_mul_eq_mul_left ht0 huv)]
        simp only [Nat.mul_div_cancel_left _ ht0, mul_sum]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun q hq hnot => hnonneg t q)
  calc
    _ ≤ ∑ t ∈ T, ∑ q ∈ (squarefreeUpTo R).filter (t ∣ ·),
        (t : ℝ) * b t * primeProduct κ (q/t) := sum_le_sum hsingle
    _ = ∑ q ∈ squarefreeUpTo R, ∑ t ∈ T.filter (· ∣ q),
        (t : ℝ) * b t * primeProduct κ (q/t) := by
      simp only [sum_filter]
      rw [sum_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro q hq
      have hq0 : q ≠ 0 := by have := (mem_Icc.mp (mem_filter.mp hq).1).1; omega
      apply sum_le_sum_of_subset_of_nonneg
      · intro t ht
        exact Nat.mem_divisors.mpr ⟨(mem_filter.mp ht).2, hq0⟩
      · intro t ht hnot
        exact hnonneg t q

theorem mul_div_ge_half {R t : ℕ} (ht : 0 < t) (htr : t ≤ R) :
    (R : ℝ) / 2 ≤ (t : ℝ) * (R/t : ℕ) := by
  have hd : 1 ≤ R/t := (Nat.le_div_iff_mul_le ht).mpr (by simpa using htr)
  have hrem := Nat.mod_lt R ht
  have hrepr := Nat.mod_add_div R t
  have hmul : t ≤ t * (R/t) := by simpa using Nat.mul_le_mul_left t hd
  have h : R ≤ 2 * (t * (R/t)) := by omega
  have hr : (R : ℝ) ≤ 2 * ((t : ℝ) * (R/t : ℕ)) := by exact_mod_cast h
  linarith

theorem weighted_centered_budget (R : ℕ) (T : Finset ℕ) (b κ : ℕ → ℝ)
    (hb : ∀ t, 0 ≤ b t) (hκ : ∀ p, 0 < κ p)
    (hT : ∀ t ∈ T, Squarefree t ∧ t ≤ R) {B : ℝ} (hB : 0 < B)
    (hcop : ∀ t ∈ T, ∑ p ∈ t.primeFactors, (1 : ℝ) / p ≤ 1/16)
    (hmean : ∑ p ∈ primesUpTo R, |Real.log (κ p)| / p ≤ B/16) :
    ((R : ℝ) / 16 * Real.exp (-B)) * (∑ t ∈ T, b t) ≤
      ∑ q ∈ squarefreeUpTo R, ∑ t ∈ q.divisors,
        (t : ℝ) * b t * primeProduct κ (q/t) := by
  have hone (t : ℕ) (ht : t ∈ T) :
      ((R : ℝ) / 16 * Real.exp (-B)) * b t ≤
      (t : ℝ) * b t * ∑ u ∈ completions (R/t) t, primeProduct κ u := by
    have ht0 := (hT t ht).1.ne_zero.bot_lt
    have hm : ∑ p ∈ primesUpTo (R/t), |Real.log (κ p)| / p ≤ B/16 := by
      apply le_trans _ hmean
      apply sum_le_sum_of_subset_of_nonneg (primesUpTo_mono (Nat.div_le_self R t))
      intro p hp hnot
      positivity
    have hw := sum_primeProduct_ge (R/t) t (hT t ht).1.ne_zero κ hκ hB (hcop t ht) hm
    have hround := mul_div_ge_half ht0 (hT t ht).2
    calc
      _ = ((R : ℝ)/2) * (Real.exp (-B)/8) * b t := by ring
      _ ≤ ((t : ℝ) * (R/t : ℕ)) * (Real.exp (-B)/8) * b t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hround (by positivity)) (hb t)
      _ = (t : ℝ) * b t * (((R/t : ℕ) : ℝ)/8 * Real.exp (-B)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (mul_nonneg (Nat.cast_nonneg _) (hb t))
  calc
    _ = ∑ t ∈ T, ((R : ℝ)/16 * Real.exp (-B)) * b t := mul_sum ..
    _ ≤ ∑ t ∈ T, (t : ℝ) * b t *
        ∑ u ∈ completions (R/t) t, primeProduct κ u := sum_le_sum hone
    _ ≤ _ := sum_completion_pairs_le R T b κ hb (fun p => (hκ p).le) (fun t ht => (hT t ht).1)

end Ostmann.Supply.CompletionCounting

end

end OAI
