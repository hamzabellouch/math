import OAI.NumberTheory.TwoPoint.Walks.ProhibitedWords
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-!
# The shortest-gap argument for perfect blocks

The finite combinatorial lemma isolates a shortest gap across all prime
coordinates. Every label has interval-shaped uses inside the intervening
substring. The arithmetic lemmas below use exact integer displacement sums.
-/

namespace TwoPointCorrelations

open Finset

/-- Interval-shaped occurrence sets on a half-open range of positions. -/
def OccurrenceIntervals {α : Type*} (P : α → ℕ → Prop) (a b : ℕ) : Prop :=
  ∀ p i j k, a ≤ i → i ≤ j → j ≤ k → k < b → P p i → P p k → P p j

/-- An occurrence gap has present endpoints and an absent interior position. -/
def OccurrenceHole {α : Type*} (P : α → ℕ → Prop) (n : ℕ) (p : α) (i j : ℕ) : Prop :=
  i < j ∧ j < n ∧ P p i ∧ P p j ∧ ∃ k, i < k ∧ k < j ∧ ¬P p k

lemma not_occurrenceIntervals_iff {α : Type*} (P : α → ℕ → Prop) (n : ℕ) :
    ¬OccurrenceIntervals P 0 n ↔ ∃ p i j, OccurrenceHole P n p i j := by
  classical
  constructor
  · intro h
    simp only [OccurrenceIntervals, not_forall] at h
    obtain ⟨p, i, k, j, h⟩ := h
    obtain ⟨_, hik, hkj, hjn, hpi, hpj, hpk⟩ := h
    have hik' : i < k := lt_of_le_of_ne hik (fun heq => hpk (heq ▸ hpi))
    have hkj' : k < j := lt_of_le_of_ne hkj (fun heq => hpk (heq.symm ▸ hpj))
    exact ⟨p, i, j, hik'.trans hkj', hjn, hpi, hpj, k, hik', hkj', hpk⟩
  · rintro ⟨p, i, j, hij, hjn, hpi, hpj, k, hik, hkj, hpk⟩ h
    exact hpk (h p i k j (Nat.zero_le _) hik.le hkj.le hjn hpi hpj)

/-- A shortest gap has no appearances of its own label in its interior, and
all labels have interval-shaped appearances before its returning endpoint. -/
theorem exists_shortest_occurrence_hole {α : Type*} (P : α → ℕ → Prop) (n : ℕ)
    (h : ¬OccurrenceIntervals P 0 n) :
    ∃ p i j, OccurrenceHole P n p i j ∧
      (∀ k, i < k → k < j → ¬P p k) ∧ OccurrenceIntervals P i j := by
  classical
  obtain ⟨p, i, j, hgap⟩ := (not_occurrenceIntervals_iff P n).mp h
  have hex : ∃ d : ℕ, ∃ p i j, OccurrenceHole P n p i j ∧ j - i = d :=
    ⟨j - i, p, i, j, hgap, rfl⟩
  obtain ⟨p, i, j, hgap, hlength⟩ := Nat.find_spec hex
  have hmin (q : α) (u v : ℕ) (huv : OccurrenceHole P n q u v) : j - i ≤ v - u := by
    have h := Nat.find_min' hex ⟨q, u, v, huv, rfl⟩
    omega
  rcases hgap with ⟨hij, hjn, hpi, hpj, r, hir, hrj, hpr⟩
  refine ⟨p, i, j, ⟨hij, hjn, hpi, hpj, r, hir, hrj, hpr⟩, ?_, ?_⟩
  · intro k hik hkj hpk
    rcases lt_trichotomy r k with hrk | hrk | hrk
    · have h := hmin p i k ⟨hik, hkj.trans hjn, hpi, hpk, r, hir, hrk, hpr⟩
      omega
    · exact hpr (hrk ▸ hpk)
    · have h := hmin p k j ⟨hkj, hjn, hpk, hpj, r, hrk, hrj, hpr⟩
      omega
  · intro q a b c hia hab hbc hcj hqa hqc
    by_contra hqb
    have hab' : a < b := lt_of_le_of_ne hab (fun heq => hqb (heq ▸ hqa))
    have hbc' : b < c := lt_of_le_of_ne hbc (fun heq => hqb (heq.symm ▸ hqc))
    have h := hmin q a c ⟨hab'.trans hbc', hcj.trans hjn, hqa, hqc, b, hab', hbc', hqb⟩
    omega

/-- Displacement of the contiguous positions `a, ..., b-1`. -/
def intervalDisplacement (D : ℕ → ℤ) (a b : ℕ) : ℤ := ∑ i ∈ Ico a b, D i

lemma intervalDisplacement_eq_sub (D : ℕ → ℤ) {a b : ℕ} (hab : a ≤ b) :
    intervalDisplacement D a b = (∑ i ∈ range b, D i) - ∑ i ∈ range a, D i :=
  sum_Ico_eq_sub D hab

lemma intervalDisplacement_cons (D : ℕ → ℤ) {a b : ℕ} (hab : a < b) :
    intervalDisplacement D a b = D a + intervalDisplacement D (a + 1) b := by
  rw [intervalDisplacement_eq_sub D hab.le,
    intervalDisplacement_eq_sub D (by omega), sum_range_succ]
  ring

@[simp] lemma intervalDisplacement_singleton (D : ℕ → ℤ) (a : ℕ) :
    intervalDisplacement D a (a + 1) = D a := by simp [intervalDisplacement]

/-- A concrete local prohibition, including the complete occurrence pattern
and an interior suffix divisibility relation. -/
def ProhibitedInterval {α : Type*} (P : α → ℕ → Prop) (D : ℕ → ℤ)
    (prime : α → ℕ) (a b : ℕ) : Prop :=
  a + 2 < b ∧ OccurrenceIntervals P a b ∧
  ∃ p, P p a ∧ ¬P p (b - 1) ∧ ∃ c, a < c ∧ c + 1 < b ∧
    (prime p : ℤ) ∣ intervalDisplacement D c b

/-- Positivity at two departures supplies the divisibility of the intervening
sum, with no assertion of independence between the sites. -/
lemma departure_difference_dvd {α : Type*} (P : α → ℕ → Prop) (D : ℕ → ℤ)
    (prime : α → ℕ) (x : ℤ) (n : ℕ)
    (hpositive : ∀ p i, i < n → P p i → (prime p : ℤ) ∣ x + ∑ a ∈ range i, D a)
    {p : α} {i j : ℕ} (hij : i ≤ j) (hj : j < n) (hi : P p i) (hjP : P p j) :
    (prime p : ℤ) ∣ intervalDisplacement D i j := by
  have hleft := hpositive p i (lt_of_le_of_lt hij hj) hi
  have hright := hpositive p j hj hjP
  have hsub := hright.sub hleft
  rw [intervalDisplacement_eq_sub D hij]
  convert hsub using 1; ring

/-- The shortest returning prime would give a prohibited subword. Thus a
positive block avoiding those words has interval-shaped prime occurrences. -/
theorem block_occurrence_intervals {α : Type*} (P : α → ℕ → Prop) (D : ℕ → ℤ)
    (prime : α → ℕ) (x : ℤ) (n : ℕ)
    (hpositive : ∀ p i, i < n → P p i → (prime p : ℤ) ∣ x + ∑ a ∈ range i, D a)
    (hon : ∀ p i, i < n → P p i → (prime p : ℤ) ∣ D i)
    (hoff : ∀ p i, (∃ j, j < n ∧ P p j) → i < n → ¬P p i → ¬(prime p : ℤ) ∣ D i)
    (havoid : ∀ a b, b ≤ n → ¬ProhibitedInterval P D prime a b) :
    OccurrenceIntervals P 0 n := by
  classical
  by_contra h
  obtain ⟨p, i, j, hhole, hgap, hlocal⟩ := exists_shortest_occurrence_hole P n h
  obtain ⟨hij, hjn, hpi, hpj, k, hik, hkj, _⟩ := hhole
  have hsum := departure_difference_dvd P D prime x n hpositive hij.le hjn hpi hpj
  have hfirst := hon p i (hij.trans hjn) hpi
  have htail : (prime p : ℤ) ∣ intervalDisplacement D (i + 1) j := by
    rw [intervalDisplacement_cons D hij] at hsum
    have hd := hsum.sub hfirst
    convert hd using 1; ring
  have hlength : i + 2 < j := by
    by_contra hlen
    have heq : j = i + 2 := by omega
    subst j
    rw [show i + 2 = (i + 1) + 1 by omega, intervalDisplacement_singleton] at htail
    exact hoff p (i + 1) ⟨i, by omega, hpi⟩ (by omega) (hgap (i + 1) (by omega) (by omega)) htail
  apply havoid i j hjn.le
  exact ⟨hlength, hlocal, p, hpi, hgap (j - 1) (by omega) (by omega),
    i + 1, by omega, by omega, htail⟩

/-- Once occurrences are intervals, a directed change in the first two
prime tuples supplies a prime absent from the final tuple. Any zero sum
then gives the same prohibited suffix relation. -/
theorem block_nonzero_subintervals {α : Type*} (P : α → ℕ → Prop) (D : ℕ → ℤ)
    (prime : α → ℕ) (n : ℕ) (hinterval : OccurrenceIntervals P 0 n)
    (hon : ∀ p i, i < n → P p i → (prime p : ℤ) ∣ D i)
    (hoff : ∀ p i, (∃ j, j < n ∧ P p j) → i < n → ¬P p i → ¬(prime p : ℤ) ∣ D i)
    (hstep : ∀ i, i < n → D i ≠ 0)
    (hchange : ∀ i, i + 1 < n → ∃ p, P p i ∧ ¬P p (i + 1))
    (havoid : ∀ a b, b ≤ n → ¬ProhibitedInterval P D prime a b) :
    ∀ a b, a < b → b ≤ n → intervalDisplacement D a b ≠ 0 := by
  intro a b hab hbn hzero
  by_cases hshort : b = a + 1
  · subst b
    exact hstep a (by omega) (by simpa using hzero)
  have hab2 : a + 1 < b := by omega
  obtain ⟨p, hpa, hpnext⟩ := hchange a (by omega)
  have hplast : ¬P p (b - 1) := by
    intro hp
    exact hpnext (hinterval p a (a + 1) (b - 1) (Nat.zero_le _) (by omega)
      (by omega) (by omega) hpa hp)
  have htail : (prime p : ℤ) ∣ intervalDisplacement D (a + 1) b := by
    have hfirst := hon p a (by omega) hpa
    rw [intervalDisplacement_cons D hab] at hzero
    have heq : intervalDisplacement D (a + 1) b = -D a := by omega
    rw [heq]
    exact hfirst.neg_right
  by_cases htwo : b = a + 2
  · subst b
    rw [show a + 2 = (a + 1) + 1 by omega, intervalDisplacement_singleton] at htail
    exact hoff p (a + 1) ⟨a, by omega, hpa⟩ (by omega) hpnext htail
  apply havoid a b hbn
  refine ⟨by omega, ?_, p, hpa, hplast, a + 1, by omega, by omega, htail⟩
  intro q i j k hai hij hjk hkb hqi hqk
  exact hinterval q i j k (by omega) hij hjk (by omega) hqi hqk

end TwoPointCorrelations

end OAI
