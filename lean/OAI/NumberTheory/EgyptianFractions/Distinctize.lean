import OAI.NumberTheory.EgyptianFractions.FixedSumFinite

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337
namespace Distinctize

/-- Takenouchi's two-term replacement increases the denominator sum. -/
theorem duplicate_split (d : ℕ) (hd : 3 ≤ d) :
    ∃ u v : ℕ, 2 ≤ u ∧ 2 ≤ v ∧
      (2 : ℚ) / d = 1 / (u : ℚ) + 1 / (v : ℚ) ∧ 2 * d < u + v := by
  let p := d / 2
  have hdiv := Nat.mod_add_div d 2
  by_cases heven : d % 2 = 0
  · have hdp : d = 2 * p := by omega
    have hp : 2 ≤ p := by omega
    refine ⟨p + 1, p * (p + 1), by omega, by nlinarith, ?_, ?_⟩
    · rw [hdp]
      push_cast
      have hp0 : (p : ℚ) ≠ 0 := by positivity
      have hp1 : (p : ℚ) + 1 ≠ 0 := by positivity
      field_simp
    · rw [hdp]
      nlinarith [sq_nonneg (p - 2 : ℤ)]
  · have hdp : d = 2 * p + 1 := by omega
    have hp : 1 ≤ p := by omega
    refine ⟨p + 1, (p + 1) * (2 * p + 1), by omega, by nlinarith, ?_, ?_⟩
    · rw [hdp]
      push_cast
      have hp1 : (p : ℚ) + 1 ≠ 0 := by positivity
      have hp2 : 2 * (p : ℚ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    · rw [hdp]
      nlinarith

/-- Updating one coordinate changes a sum by the corresponding summand. -/
theorem sum_update_balance {k : ℕ} (n : Fin k → ℕ) (g : ℕ → ℚ)
    (i : Fin k) (u : ℕ) :
    (∑ j, g (Function.update n i u j)) + g (n i) =
      (∑ j, g (n j)) + g u := by
  have hfun : (fun j => g (Function.update n i u j)) =
      Function.update (fun j => g (n j)) i (g u) := by
    funext j
    exact Function.apply_update (fun _ => g) n i u j
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ (fun j => g (n j)) (Finset.mem_univ i)
  linarith

/-- Replace equal coordinates by a two-term replacement. -/
theorem two_updates {k : ℕ} (n : Fin k → ℕ) (g : ℕ → ℚ)
    (i j : Fin k) (hij : i ≠ j) (u v : ℕ) :
    (∑ a, g (Function.update (Function.update n i u) j v a)) +
        g (n i) + g (n j) =
      (∑ a, g (n a)) + g u + g v := by
  have hi := sum_update_balance n g i u
  have hj := sum_update_balance (Function.update n i u) g j v
  rw [Function.update_of_ne hij.symm] at hj
  linarith

/-- Takenouchi's finite maximization argument removes all repetitions. -/
theorem distinctize_of_finite {k : ℕ} {x : ℚ} (_hx : 0 < x) (hxone : x < 1)
    (hfinite : Set.Finite {n : Fin k → ℕ | (∀ i, 0 < n i) ∧ Monotone n ∧
      (∑ i, (1 : ℚ) / (n i : ℚ)) = x})
    (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i, (1 : ℚ) / (n i : ℚ)) = x) :
    ∃ d : Fin k → ℕ, (∀ i, 2 ≤ d i) ∧ StrictMono d ∧
      (∑ i, (1 : ℚ) / (d i : ℚ)) = x := by
  let S : Set (Fin k → ℕ) := {d | (∀ i, 0 < d i) ∧ Monotone d ∧
      (∑ i, (1 : ℚ) / (d i : ℚ)) = x}
  have hS : S.Nonempty := by
    refine ⟨n ∘ Tuple.sort n, (fun i => hn _), Tuple.monotone_sort n, ?_⟩
    calc
      _ = ∑ i, (1 : ℚ) / (n i : ℚ) :=
        Equiv.sum_comp (Tuple.sort n) (fun i => (1 : ℚ) / (n i : ℚ))
      _ = x := hsum
  obtain ⟨d, hd, hmax⟩ := Set.exists_max_image S
    (fun d => ∑ i, (d i : ℚ)) hfinite hS
  have hdpos : ∀ i, 0 < d i := hd.1
  have hdmono : Monotone d := hd.2.1
  have hdsum : (∑ i, (1 : ℚ) / (d i : ℚ)) = x := hd.2.2
  have hdtwo : ∀ i, 2 ≤ d i := by
    intro i
    have hsingle : (1 : ℚ) / (d i : ℚ) ≤ x := by
      rw [← hdsum]
      exact Finset.single_le_sum (f := fun j => (1 : ℚ) / (d j : ℚ))
        (by intro j hj; positivity) (Finset.mem_univ i)
    by_contra h
    have hdi : d i = 1 := by have := hdpos i; omega
    rw [hdi] at hsingle
    norm_num at hsingle
    linarith
  refine ⟨d, hdtwo, hdmono.strictMono_iff_injective.mpr ?_, hdsum⟩
  intro i j heq
  by_contra hij
  have hpair : (1 : ℚ) / (d i : ℚ) + 1 / (d j : ℚ) ≤ x := by
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun a => (1 : ℚ) / (d a : ℚ))
      (Finset.subset_univ {i, j}) (by intro a ha hnot; positivity)
    rw [Finset.sum_pair hij, hdsum] at hle
    exact hle
  have hdthree : 3 ≤ d i := by
    by_contra h
    have hdi : d i = 2 := by have := hdtwo i; omega
    rw [← heq, hdi] at hpair
    norm_num at hpair
    linarith
  obtain ⟨u, v, hu, hv, hsplit, hincrease⟩ := duplicate_split (d i) hdthree
  let e := Function.update (Function.update d i u) j v
  have hepos : ∀ a, 0 < e a := by
    intro a
    simp only [e, Function.update_apply]
    split_ifs <;> first | omega | exact hdpos a
  have hesum : (∑ a, (1 : ℚ) / (e a : ℚ)) = x := by
    have hbal := two_updates d (fun t => (1 : ℚ) / (t : ℚ)) i j hij u v
    change (∑ a, (1 : ℚ) / (e a : ℚ)) + 1 / (d i : ℚ) + 1 / (d j : ℚ) =
      (∑ a, (1 : ℚ) / (d a : ℚ)) + 1 / (u : ℚ) + 1 / (v : ℚ) at hbal
    rw [hdsum, ← heq] at hbal
    rw [show (2 : ℚ) / (d i : ℚ) = 1 / (d i : ℚ) + 1 / (d i : ℚ) by ring] at hsplit
    linarith [hsplit]
  have hegreater : (∑ a, (d a : ℚ)) < ∑ a, (e a : ℚ) := by
    have hbal := two_updates d (fun t => (t : ℚ)) i j hij u v
    change (∑ a, (e a : ℚ)) + (d i : ℚ) + (d j : ℚ) =
      (∑ a, (d a : ℚ)) + (u : ℚ) + (v : ℚ) at hbal
    rw [← heq] at hbal
    have hinc : 2 * (d i : ℚ) < (u : ℚ) + (v : ℚ) := by exact_mod_cast hincrease
    linarith
  have heS : e ∘ Tuple.sort e ∈ S := by
    refine ⟨(fun a => hepos _), Tuple.monotone_sort e, ?_⟩
    calc
      _ = ∑ a, (1 : ℚ) / (e a : ℚ) :=
        Equiv.sum_comp (Tuple.sort e) (fun a => (1 : ℚ) / (e a : ℚ))
      _ = x := hesum
  have hle := hmax (e ∘ Tuple.sort e) heS
  have heperm : (∑ a, ((e ∘ Tuple.sort e) a : ℚ)) = ∑ a, (e a : ℚ) :=
    Equiv.sum_comp (Tuple.sort e) (fun a => (e a : ℚ))
  rw [heperm] at hle
  linarith

/-- Every positive rational unit-fraction list of total less than one has a
strictly increasing representation with exactly the same number of terms. -/
theorem distinctize {k : ℕ} {x : ℚ} (hx : 0 < x) (hxone : x < 1)
    (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i, (1 : ℚ) / (n i : ℚ)) = x) :
    ∃ d : Fin k → ℕ, (∀ i, 2 ≤ d i) ∧ StrictMono d ∧
      (∑ i, (1 : ℚ) / (d i : ℚ)) = x :=
  distinctize_of_finite hx hxone (ordered_unit_sums_finite k x) n hn hsum

end Distinctize
end Problem337

end

end OAI
