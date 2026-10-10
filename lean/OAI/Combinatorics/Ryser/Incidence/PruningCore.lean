import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace RyserCoveringCounterexample.Incidence

variable {Pt Ln : Type*} [instDecidableEqPt : DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

def leftDegree (R : Pt → Ln → Prop) (L : Finset Ln) (p : Pt) : ℕ := by
  classical
  exact (L.filter (R p)).card

def rightDegree (R : Pt → Ln → Prop) (P : Finset Pt) (l : Ln) : ℕ :=
  leftDegree (fun l p => R p l) P l

def incidenceCount (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln) : ℕ :=
  ∑ p ∈ P, leftDegree R L p

theorem leftDegree_eq_sum (R : Pt → Ln → Prop) (L : Finset Ln) (p : Pt) :
    leftDegree R L p = ∑ l ∈ L, if R p l then 1 else 0 := let _ := instDecidableEqPt; let _ := instDecidableEqLn; by
  classical
  exact (Finset.sum_boole (R := ℕ) (R p) L).symm

theorem incidenceCount_swap (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln) :
    incidenceCount R P L = incidenceCount (fun l p => R p l) L P := by
  classical
  simp only [incidenceCount, leftDegree_eq_sum]
  exact Finset.sum_comm

theorem leftDegree_mono (R : Pt → Ln → Prop) {L L' : Finset Ln}
    (hL : L ⊆ L') (p : Pt) : leftDegree R L p ≤ leftDegree R L' p := let _ := instDecidableEqPt; let _ := instDecidableEqLn; by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter (R p) hL)

theorem rightDegree_mono (R : Pt → Ln → Prop) {P P' : Finset Pt}
    (hP : P ⊆ P') (l : Ln) : rightDegree R P l ≤ rightDegree R P' l :=
  leftDegree_mono (fun l p => R p l) hP l

theorem incidenceCount_erase_left (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) {p : Pt} (hp : p ∈ P) :
    incidenceCount R (P.erase p) L + leftDegree R L p = incidenceCount R P L := let _ := instDecidableEqLn;
  Finset.sum_erase_add P (leftDegree R L) hp

theorem incidenceCount_erase_right (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) {l : Ln} (hl : l ∈ L) :
    incidenceCount R P (L.erase l) + rightDegree R P l = incidenceCount R P L := by
  rw [incidenceCount_swap R P (L.erase l), incidenceCount_swap R P L]
  exact incidenceCount_erase_left (fun l p => R p l) L P hl

def pruningPotential (R : Pt → Ln → Prop) (d : ℝ) (P : Finset Pt) (L : Finset Ln) : ℝ :=
  (incidenceCount R P L : ℝ) - d * ((P.card : ℝ) + (L.card : ℝ))

theorem pruningPotential_le_erase_left (R : Pt → Ln → Prop) (d : ℝ)
    (P : Finset Pt) (L : Finset Ln) {p : Pt} (hp : p ∈ P)
    (hdeg : (leftDegree R L p : ℝ) ≤ d) :
    pruningPotential R d P L ≤ pruningPotential R d (P.erase p) L := by
  have hcount : (incidenceCount R (P.erase p) L : ℝ) + (leftDegree R L p : ℝ) =
      (incidenceCount R P L : ℝ) := by
    exact_mod_cast incidenceCount_erase_left R P L hp
  have hcard : ((P.erase p).card : ℝ) + 1 = (P.card : ℝ) := by
    exact_mod_cast Finset.card_erase_add_one hp
  unfold pruningPotential
  rw [← hcount, ← hcard]
  nlinarith

theorem pruningPotential_le_erase_right (R : Pt → Ln → Prop) (d : ℝ)
    (P : Finset Pt) (L : Finset Ln) {l : Ln} (hl : l ∈ L)
    (hdeg : (rightDegree R P l : ℝ) ≤ d) :
    pruningPotential R d P L ≤ pruningPotential R d P (L.erase l) := by
  have hcount : (incidenceCount R P (L.erase l) : ℝ) + (rightDegree R P l : ℝ) =
      (incidenceCount R P L : ℝ) := by
    exact_mod_cast incidenceCount_erase_right R P L hl
  have hcard : ((L.erase l).card : ℝ) + 1 = (L.card : ℝ) := by
    exact_mod_cast Finset.card_erase_add_one hl
  unfold pruningPotential
  rw [← hcount, ← hcard]
  nlinarith

def MinimumDegrees (R : Pt → Ln → Prop) (d : ℝ) (P : Finset Pt) (L : Finset Ln) : Prop :=
  (∀ p ∈ P, d ≤ (leftDegree R L p : ℝ)) ∧
    (∀ l ∈ L, d ≤ (rightDegree R P l : ℝ))

private theorem exists_degree_core_aux (R : Pt → Ln → Prop) (d : ℝ) (n : ℕ) :
    ∀ (P : Finset Pt) (L : Finset Ln), P.card + L.card = n →
      ∃ P' : Finset Pt, P' ⊆ P ∧ ∃ L' : Finset Ln, L' ⊆ L ∧
        MinimumDegrees R d P' L' ∧ pruningPotential R d P L ≤ pruningPotential R d P' L' := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P L hsize
    by_cases hpmin : ∀ p ∈ P, d ≤ (leftDegree R L p : ℝ)
    · by_cases hlmin : ∀ l ∈ L, d ≤ (rightDegree R P l : ℝ)
      · exact ⟨P, Finset.Subset.refl _, L, Finset.Subset.refl _, ⟨hpmin, hlmin⟩, le_rfl⟩
      · have hex : ∃ l ∈ L, (rightDegree R P l : ℝ) < d := by
          by_contra hnone
          apply hlmin
          intro l hl
          apply le_of_not_gt
          intro hdeg
          exact hnone ⟨l, hl, hdeg⟩
        obtain ⟨l, hl, hdeg⟩ := hex
        have hlt : P.card + (L.erase l).card < n := by
          rw [← hsize]
          exact Nat.add_lt_add_left (Finset.card_erase_lt_of_mem hl) _
        obtain ⟨P', hP', L', hL', hmin, hpot⟩ := ih _ hlt P (L.erase l) rfl
        exact ⟨P', hP', L', hL'.trans (Finset.erase_subset _ _), hmin,
          (pruningPotential_le_erase_right R d P L hl hdeg.le).trans hpot⟩
    · have hex : ∃ p ∈ P, (leftDegree R L p : ℝ) < d := by
        by_contra hnone
        apply hpmin
        intro p hp
        apply le_of_not_gt
        intro hdeg
        exact hnone ⟨p, hp, hdeg⟩
      obtain ⟨p, hp, hdeg⟩ := hex
      have hlt : (P.erase p).card + L.card < n := by
        rw [← hsize]
        exact Nat.add_lt_add_right (Finset.card_erase_lt_of_mem hp) _
      obtain ⟨P', hP', L', hL', hmin, hpot⟩ := ih _ hlt (P.erase p) L rfl
      exact ⟨P', hP'.trans (Finset.erase_subset _ _), L', hL', hmin,
        (pruningPotential_le_erase_left R d P L hp hdeg.le).trans hpot⟩

theorem exists_degree_core (R : Pt → Ln → Prop) (d : ℝ) (P : Finset Pt) (L : Finset Ln) :
    ∃ P' : Finset Pt, P' ⊆ P ∧ ∃ L' : Finset Ln, L' ⊆ L ∧
      MinimumDegrees R d P' L' ∧ pruningPotential R d P L ≤ pruningPotential R d P' L' :=
  exists_degree_core_aux R d (P.card + L.card) P L rfl

theorem degree_core_incidence_lower_bound (R : Pt → Ln → Prop) {d : ℝ} (hd : 0 ≤ d)
    (P P' : Finset Pt) (L L' : Finset Ln)
    (hpot : pruningPotential R d P L ≤ pruningPotential R d P' L') :
    (incidenceCount R P L : ℝ) - d * ((P.card : ℝ) + (L.card : ℝ)) ≤
      (incidenceCount R P' L' : ℝ) := let _ := instDecidableEqPt; let _ := instDecidableEqLn; by
  have hnonneg : 0 ≤ d * ((P'.card : ℝ) + (L'.card : ℝ)) :=
    mul_nonneg hd (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  unfold pruningPotential at hpot
  linarith

end RyserCoveringCounterexample.Incidence

end

end OAI
