import OAI.NumberTheory.Ostmann.Statement

namespace OAI

namespace Ostmann.Supply.CompletionCounting
open Finset

def multiplesUpTo (U d : ℕ) : Finset ℕ := (Icc 1 U).filter (d ∣ ·)

@[simp] theorem card_multiplesUpTo (U d : ℕ) :
    (multiplesUpTo U d).card = U / d := by
  have h : Icc 1 U = Ioc 0 U := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  simpa [multiplesUpTo, h] using Nat.Ioc_filter_dvd_card_eq_div U d

theorem card_multiplesUpTo_le (U d : ℕ) :
    ((multiplesUpTo U d).card : ℝ) ≤ (U : ℝ) / d := by
  rw [card_multiplesUpTo]
  exact Nat.cast_div_le

theorem sum_inverse_sq_le (U : ℕ) :
    ∑ d ∈ Icc 2 U, (1 : ℝ) / (d : ℝ)^2 ≤ 3 / 4 := by
  have hmain : ∀ n : ℕ, 2 ≤ n →
      ∑ d ∈ Icc 2 n, (1 : ℝ) / (d : ℝ)^2 ≤ 3 / 4 - 1 / n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [sum_Icc_succ_top (by omega)]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hstep : (1 : ℝ) / (n + 1)^2 ≤ 1 / n - 1 / (n + 1) := by
        field_simp
        nlinarith
      push_cast
      linarith
  by_cases hU : 2 ≤ U
  · exact (hmain U hU).trans (sub_le_self _ (by positivity))
  · have h : Icc 2 U = ∅ := Icc_eq_empty_of_lt (by omega)
    norm_num [h]

theorem card_dvd_union_le (U : ℕ) (s : Finset ℕ) (d : ℕ → ℕ) :
    ((s.biUnion (fun p => multiplesUpTo U (d p))).card : ℝ) ≤
      (U : ℝ) * ∑ p ∈ s, (1 : ℝ) / d p := by
  calc
    _ ≤ ∑ p ∈ s, ((multiplesUpTo U (d p)).card : ℝ) := by
      exact_mod_cast (card_biUnion_le (s := s) (t := fun p => multiplesUpTo U (d p)))
    _ ≤ ∑ p ∈ s, (U : ℝ) / d p := sum_le_sum (fun p _ => card_multiplesUpTo_le U (d p))
    _ = _ := by rw [mul_sum]; congr 1; ext p; ring

theorem card_nonsquarefree_le (U : ℕ) :
    (((Icc 1 U).filter (fun u => ¬Squarefree u)).card : ℝ) ≤ 3 * U / 4 := by
  have hsub : (Icc 1 U).filter (fun u => ¬Squarefree u) ⊆
      (Icc 2 U).biUnion (fun p => multiplesUpTo U (p*p)) := by
    intro u hu
    obtain ⟨hu, hsq⟩ := mem_filter.mp hu
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    push Not at hsq
    obtain ⟨p, hp, hpu⟩ := hsq
    have hpu' : p ∣ u := dvd_trans (dvd_mul_right p p) hpu
    have hple : p ≤ u := Nat.le_of_dvd (by have := (mem_Icc.mp hu).1; omega) hpu'
    exact mem_biUnion.mpr ⟨p, mem_Icc.mpr ⟨hp.two_le, hple.trans (mem_Icc.mp hu).2⟩,
      mem_filter.mpr ⟨hu, hpu⟩⟩
  calc
    _ ≤ (((Icc 2 U).biUnion (fun p => multiplesUpTo U (p*p))).card : ℝ) :=
      Nat.cast_le.mpr (card_le_card hsub)
    _ ≤ (U : ℝ) * ∑ p ∈ Icc 2 U, (1 : ℝ) / (p*p : ℕ) :=
      card_dvd_union_le U (Icc 2 U) (fun p => p*p)
    _ = (U : ℝ) * ∑ p ∈ Icc 2 U, (1 : ℝ) / (p : ℝ)^2 := by simp [pow_two]
    _ ≤ (U : ℝ) * (3/4) := mul_le_mul_of_nonneg_left (sum_inverse_sq_le U) (by positivity)
    _ = _ := by ring

theorem card_noncoprime_le (U t : ℕ) (ht : t ≠ 0) :
    (((Icc 1 U).filter (fun u => ¬Nat.Coprime u t)).card : ℝ) ≤
      (U : ℝ) * ∑ p ∈ t.primeFactors, (1 : ℝ) / p := by
  have hsub : (Icc 1 U).filter (fun u => ¬Nat.Coprime u t) ⊆
      t.primeFactors.biUnion (fun p => multiplesUpTo U p) := by
    intro u hu
    obtain ⟨hu, hcop⟩ := mem_filter.mp hu
    obtain ⟨p, hp, hpu, hpt⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    exact mem_biUnion.mpr ⟨p, hp.mem_primeFactors hpt ht, mem_filter.mpr ⟨hu, hpu⟩⟩
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans (card_dvd_union_le U t.primeFactors id)

end Ostmann.Supply.CompletionCounting

end OAI
