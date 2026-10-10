import OAI.Geometry.PeriodicTiling.FinitePairCounting
import OAI.Geometry.PeriodicTiling.PrimeDifferencePairs
import OAI.Geometry.PeriodicTiling.FullDifferenceBound
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

noncomputable section

namespace PeriodicTilingThree

open Classical
open scoped BigOperators

abbrev Coloring (q s : ℕ) := ZMod q → Fin s

def BadDifference {q s : ℕ} (c : Coloring q s) (ν : Fin s) (d : ZMod q) : Prop :=
  ¬ ∃ x y, c x = ν ∧ c y = ν ∧ x - y = d

def badDifferenceColorings {q s : ℕ} [NeZero q]
    (ν : Fin s) (d : ZMod q) : Finset (Coloring q s) :=
  Finset.univ.filter (fun c => BadDifference c ν d)

@[simp]
theorem mem_badDifferenceColorings {q s : ℕ} [NeZero q]
    (c : Coloring q s) (ν : Fin s) (d : ZMod q) :
    c ∈ badDifferenceColorings ν d ↔ BadDifference c ν d := by
  simp [badDifferenceColorings]

theorem badDifference_card_le {q s m : ℕ} [Fact q.Prime]
    (hq : q = 2 * m + 1) (ν : Fin s) (d : ZMod q) (hd : d ≠ 0) :
    (badDifferenceColorings ν d).card ≤ s * (s ^ 2 - 1) ^ m := by
  let pair := primeDifferencePairs q m hq d hd
  let good : Fin m → Finset (Fin s × Fin s) := fun _ => {(ν, ν)}
  have hsub : badDifferenceColorings ν d ⊆ allBadAssignments pair good := by
    intro c hc
    apply (mem_allBadAssignments pair good c).mpr
    intro j hj
    have heq : (c (pair (j, 0)), c (pair (j, 1))) = (ν, ν) :=
      Finset.mem_singleton.mp hj
    apply (mem_badDifferenceColorings c ν d).mp hc
    refine ⟨pair (j, 1), pair (j, 0), congrArg Prod.snd heq,
      congrArg Prod.fst heq, ?_⟩
    exact primeDifferencePairs_step q m hq d hd j
  have hleft : q - 2 * m = 1 := by omega
  calc
    (badDifferenceColorings ν d).card ≤ (allBadAssignments pair good).card :=
      Finset.card_le_card hsub
    _ ≤ (Fintype.card (Fin s) ^ 2 - 1) ^ m *
        Fintype.card (Fin s) ^ (Fintype.card (ZMod q) - 2 * m) :=
      allBadAssignments_card_le pair good 1 (by intro j; simp [good])
    _ = s * (s ^ 2 - 1) ^ m := by
      simp only [Fintype.card_fin, ZMod.card, hleft, pow_one]
      exact Nat.mul_comm _ _

def badDifferenceLabels (q s : ℕ) [NeZero q] : Finset (Fin s × ZMod q) :=
  Finset.univ.product ((Finset.univ : Finset (ZMod q)).erase 0)

@[simp]
theorem badDifferenceLabels_card (q s : ℕ) [NeZero q] :
    (badDifferenceLabels q s).card = s * (q - 1) := by
  simp [badDifferenceLabels, ZMod.card]

def someBadDifferenceColorings (q s : ℕ) [NeZero q] : Finset (Coloring q s) :=
  (badDifferenceLabels q s).biUnion (fun p => badDifferenceColorings p.1 p.2)

theorem someBadDifferenceColorings_card_le {q s m : ℕ} [Fact q.Prime]
    (hq : q = 2 * m + 1) :
    (someBadDifferenceColorings q s).card ≤
      (s * (q - 1)) * (s * (s ^ 2 - 1) ^ m) := by
  calc
    (someBadDifferenceColorings q s).card ≤
        ∑ p ∈ badDifferenceLabels q s, (badDifferenceColorings p.1 p.2).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ badDifferenceLabels q s, s * (s ^ 2 - 1) ^ m := by
      apply Finset.sum_le_sum
      intro p hp
      have hd : p.2 ≠ 0 := (Finset.mem_erase.mp (Finset.mem_product.mp hp).2).1
      exact badDifference_card_le hq p.1 p.2 hd
    _ = (s * (q - 1)) * (s * (s ^ 2 - 1) ^ m) := by
      rw [Finset.sum_const, nsmul_eq_mul, badDifferenceLabels_card, Nat.cast_id]

theorem exists_coloring_nonzero_differences {q s m : ℕ} [Fact q.Prime]
    (hs : 2 ≤ s) (hq : q = 2 * m + 1) (hm : 4 * s ^ 5 + 1 ≤ m) :
    ∃ c : Coloring q s, ∀ ν d, d ≠ 0 →
      ∃ x y, c x = ν ∧ c y = ν ∧ x - y = d := by
  have hspos : 0 < s := by omega
  have hstrict := Nat.mul_lt_mul_of_pos_left
    (fullDifference_bad_bound_poly s m hs hm) hspos
  have hcard : (someBadDifferenceColorings q s).card <
      (Finset.univ : Finset (Coloring q s)).card := by
    calc
      (someBadDifferenceColorings q s).card ≤
          (s * (q - 1)) * (s * (s ^ 2 - 1) ^ m) :=
        someBadDifferenceColorings_card_le hq
      _ = s * (s * (2 * m) * (s ^ 2 - 1) ^ m) := by
        rw [hq]
        simp only [Nat.add_sub_cancel]
        ring
      _ < s * s ^ (2 * m) := hstrict
      _ = (Finset.univ : Finset (Coloring q s)).card := by
        simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
        rw [hq, pow_succ]
        exact Nat.mul_comm _ _
  obtain ⟨c, _hc, hgood⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨c, ?_⟩
  intro ν d hd
  by_contra hbad
  apply hgood
  apply Finset.mem_biUnion.mpr
  refine ⟨(ν, d), ?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_erase.mpr ⟨hd, Finset.mem_univ _⟩⟩
  · exact (mem_badDifferenceColorings c ν d).mpr hbad

theorem exists_partition_of_nonzero_coloring {q s : ℕ} [Fact q.Prime]
    (c : Coloring q s)
    (hc : ∀ ν d, d ≠ 0 → ∃ x y, c x = ν ∧ c y = ν ∧ x - y = d) :
    ∃ E : Fin s → Finset (ZMod q),
      (∀ ν, (E ν).Nonempty) ∧
      (∀ x, ∃! ν, x ∈ E ν) ∧
      (∀ ν d, ∃ x ∈ E ν, ∃ y ∈ E ν, x - y = d) := by
  let E : Fin s → Finset (ZMod q) :=
    fun ν => Finset.univ.filter (fun x => c x = ν)
  have hne : ∀ ν, (E ν).Nonempty := by
    intro ν
    obtain ⟨x, _y, hx, _hy, _hxy⟩ := hc ν 1 one_ne_zero
    exact ⟨x, by simp [E, hx]⟩
  refine ⟨E, hne, ?_, ?_⟩
  · intro x
    refine ⟨c x, by simp [E], ?_⟩
    intro ν hν
    exact (Finset.mem_filter.mp hν).2.symm
  · intro ν d
    by_cases hd : d = 0
    · subst d
      obtain ⟨x, hx⟩ := hne ν
      exact ⟨x, hx, x, hx, sub_self x⟩
    · obtain ⟨x, y, hx, hy, hxy⟩ := hc ν d hd
      exact ⟨x, by simp [E, hx], y, by simp [E, hy], hxy⟩

theorem exists_fresh_prime_fullDifference_partition
    (s : ℕ) (hs : 0 < s) (forbidden : Finset ℕ) (lower : ℕ) :
    ∃ q : ℕ, q.Prime ∧ lower < q ∧ q ∉ forbidden ∧
      ∃ E : Fin s → Finset (ZMod q),
        (∀ ν, (E ν).Nonempty) ∧
        (∀ x, ∃! ν, x ∈ E ν) ∧
        (∀ ν d, ∃ x ∈ E ν, ∃ y ∈ E ν, x - y = d) := by
  let N := max (8 * s ^ 5 + 3) (max (lower + 1) (forbidden.sup id + 1))
  obtain ⟨q, hqN, hprime⟩ := Nat.exists_infinite_primes N
  have hqbig : 8 * s ^ 5 + 3 ≤ q := (le_max_left _ _).trans hqN
  have hqrest : max (lower + 1) (forbidden.sup id + 1) ≤ q :=
    (le_max_right _ _).trans hqN
  have hqlower : lower + 1 ≤ q := (le_max_left _ _).trans hqrest
  have hqforbidden : forbidden.sup id + 1 ≤ q := (le_max_right _ _).trans hqrest
  have hfresh : q ∉ forbidden := by
    intro hmem
    have hsup : q ≤ forbidden.sup id := Finset.le_sup (f := id) hmem
    omega
  have hq2 : 2 < q := by omega
  let : Fact q.Prime := ⟨hprime⟩
  refine ⟨q, hprime, by omega, hfresh, ?_⟩
  by_cases hs1 : s = 1
  · subst s
    let c : Coloring q 1 := fun _ => 0
    apply exists_partition_of_nonzero_coloring c
    intro ν d _hd
    have hν : (0 : Fin 1) = ν := Subsingleton.elim _ _
    exact ⟨d, 0, hν, hν, sub_zero d⟩
  · have hs2 : 2 ≤ s := by omega
    have hodd : q % 2 = 1 := hprime.eq_two_or_odd.resolve_left (by omega)
    let m := q / 2
    have hqm : q = 2 * m + 1 := by dsimp [m]; omega
    have hm : 4 * s ^ 5 + 1 ≤ m := by dsimp [m]; omega
    obtain ⟨c, hc⟩ := exists_coloring_nonzero_differences hs2 hqm hm
    exact exists_partition_of_nonzero_coloring c hc

end PeriodicTilingThree

end

end OAI
