import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

namespace RyserCoveringCounterexample.Incidence
attribute [local instance] Classical.propDecidable

variable {Pt Ln : Type*} [DecidableEq Pt] [instDecidableEqLn : DecidableEq Ln]

def orderedTriples (P : Finset Pt) : Finset (Σ _ : Pt, Σ _ : Pt, Pt) :=
  P.sigma fun a => (P.erase a).sigma fun b => (P.erase a).erase b

@[simp] theorem mem_orderedTriples {P : Finset Pt} {t : Σ _ : Pt, Σ _ : Pt, Pt} :
    t ∈ orderedTriples P ↔ t.1 ∈ P ∧ t.2.1 ∈ P ∧ t.2.2 ∈ P ∧
      t.2.1 ≠ t.1 ∧ t.2.2 ≠ t.1 ∧ t.2.2 ≠ t.2.1 := by
  simp only [orderedTriples, Finset.mem_sigma, Finset.mem_erase]
  simp only [and_assoc, and_left_comm, and_comm]

theorem orderedTriples_mono {P Q : Finset Pt} (hPQ : P ⊆ Q) :
    orderedTriples P ⊆ orderedTriples Q := by
  intro t ht
  obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := mem_orderedTriples.mp ht
  exact mem_orderedTriples.mpr ⟨hPQ ha, hPQ hb, hPQ hc, hab, hac, hbc⟩

theorem card_orderedTriples (P : Finset Pt) :
    (orderedTriples P).card = P.card * (P.card - 1) * (P.card - 2) := by
  simp only [orderedTriples, Finset.card_sigma]
  calc
    (∑ a ∈ P, ∑ b ∈ P.erase a, ((P.erase a).erase b).card) =
        ∑ a ∈ P, ((P.card - 1) * (P.card - 2)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hca := Finset.card_erase_of_mem ha
      calc
        (∑ b ∈ P.erase a, ((P.erase a).erase b).card) =
            ∑ b ∈ P.erase a, (P.card - 2) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.card_erase_of_mem hb, hca]
          omega
        _ = (P.card - 1) * (P.card - 2) := by
          simp only [Finset.sum_const, Nat.nsmul_eq_mul, hca]
    _ = P.card * (P.card - 1) * (P.card - 2) := by
      simp only [Finset.sum_const, Nat.nsmul_eq_mul]
      ring

theorem card_orderedTriples_real (P : Finset Pt) :
    ((orderedTriples P).card : ℝ) =
      (P.card : ℝ) * ((P.card : ℝ) - 1) * ((P.card : ℝ) - 2) := by
  rw [card_orderedTriples]
  by_cases h : 2 ≤ P.card
  · rw [Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ P.card), Nat.cast_sub h]
    norm_num
  · have hcases : P.card = 0 ∨ P.card = 1 := by omega
    rcases hcases with h | h <;> simp [h]

theorem two_ninths_cube_le_orderedTriples (P : Finset Pt) (h : 3 ≤ P.card) :
    (2 / 9 : ℝ) * (P.card : ℝ) ^ 3 ≤ ((orderedTriples P).card : ℝ) := by
  rw [card_orderedTriples_real]
  have ht : (3 : ℝ) ≤ P.card := by exact_mod_cast h
  have hprod := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr ht) (by linarith : 0 ≤ 7 * (P.card : ℝ) - 6))
    (Nat.cast_nonneg (α := ℝ) P.card)
  nlinarith

theorem sum_cube_card_sq (I : Finset Ln) (f : Ln → ℝ)
    (hf : ∀ i ∈ I, 0 ≤ f i) :
    (∑ i ∈ I, f i) ^ 3 ≤ (I.card : ℝ) ^ 2 * ∑ i ∈ I, f i ^ 3 := let _ := instDecidableEqLn; by
  by_cases hI : I.Nonempty
  · let m : ℝ := I.card
    let a : ℝ := (∑ i ∈ I, f i) / m
    have hm : 0 < m := by
      dsimp [m]
      exact_mod_cast hI.card_pos
    have ha : 0 ≤ a := div_nonneg (Finset.sum_nonneg hf) hm.le
    have heq : m * a = ∑ i ∈ I, f i := by
      dsimp [a]
      exact mul_div_cancel₀ _ (ne_of_gt hm)
    have hnon : 0 ≤ ∑ i ∈ I, (f i - a) ^ 2 * (f i + 2 * a) :=
      Finset.sum_nonneg fun i hi => mul_nonneg (sq_nonneg _) (by linarith [hf i hi])
    have hexpand : (∑ i ∈ I, (f i - a) ^ 2 * (f i + 2 * a)) =
        (∑ i ∈ I, f i ^ 3) - 3 * a ^ 2 * (∑ i ∈ I, f i) + 2 * m * a ^ 3 := by
      calc
        _ = ∑ i ∈ I, (f i ^ 3 - 3 * a ^ 2 * f i + 2 * a ^ 3) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          dsimp [m]
          ring
    rw [hexpand] at hnon
    have hc : m * a ^ 3 ≤ ∑ i ∈ I, f i ^ 3 := by
      nlinarith [congrArg (fun z : ℝ => z * a ^ 2) heq]
    have hmul := mul_le_mul_of_nonneg_left hc (sq_nonneg m)
    have hcube := congrArg (fun z : ℝ => z ^ 3) heq
    change (∑ i ∈ I, f i) ^ 3 ≤ m ^ 2 * ∑ i ∈ I, f i ^ 3
    nlinarith
  · have : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    simp [this]

def joinedNeighbors (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln)
    (x : Pt) : Finset Pt := by
  classical
  exact P.filter fun p => x ≠ p ∧ ∃ l ∈ L, R x l ∧ R p l

def anchorConfigurations (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln) :
    Finset (Σ _ : Ln, (Σ _ : Pt, Σ _ : Pt, Pt) × Pt) := by
  classical
  exact L.sigma fun l =>
    orderedTriples (P.filter fun p => R p l) ×ˢ (P.filter fun p => ¬ R p l)

def anchorWitnesses (R : Pt → Ln → Prop) (P : Finset Pt) (L : Finset Ln)
    (c : Σ _ : Ln, (Σ _ : Pt, Σ _ : Pt, Pt) × Pt) : Finset Pt := by
  classical
  exact P.filter fun x =>
    c.2.1.1 ∈ joinedNeighbors R P L x ∧
    c.2.1.2.1 ∈ joinedNeighbors R P L x ∧
    c.2.1.2.2 ∈ joinedNeighbors R P L x ∧
    c.2.2 ∈ joinedNeighbors R P L x

@[simp] theorem mem_anchorConfigurations (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln)
    (c : Σ _ : Ln, (Σ _ : Pt, Σ _ : Pt, Pt) × Pt) :
    c ∈ anchorConfigurations R P L ↔ c.1 ∈ L ∧
      c.2.1.1 ∈ P ∧ c.2.1.2.1 ∈ P ∧ c.2.1.2.2 ∈ P ∧ c.2.2 ∈ P ∧
      R c.2.1.1 c.1 ∧ R c.2.1.2.1 c.1 ∧ R c.2.1.2.2 c.1 ∧ ¬ R c.2.2 c.1 ∧
      c.2.1.2.1 ≠ c.2.1.1 ∧ c.2.1.2.2 ≠ c.2.1.1 ∧
      c.2.1.2.2 ≠ c.2.1.2.1 := let _ := instDecidableEqLn; by
  classical
  simp only [anchorConfigurations, Finset.mem_sigma, Finset.mem_product,
    mem_orderedTriples, Finset.mem_filter]
  simp only [and_assoc, and_left_comm, and_comm]

theorem anchorConfigurations_mono (R : Pt → Ln → Prop) {P Q : Finset Pt}
    (hPQ : P ⊆ Q) (L : Finset Ln) :
    anchorConfigurations R P L ⊆ anchorConfigurations R Q L := by
  intro c hc
  obtain ⟨hl, h1, h2, h3, h4, hrest⟩ := (mem_anchorConfigurations R P L c).mp hc
  exact (mem_anchorConfigurations R Q L c).mpr
    ⟨hl, hPQ h1, hPQ h2, hPQ h3, hPQ h4, hrest⟩

theorem card_anchorConfigurations (R : Pt → Ln → Prop) (P : Finset Pt)
    (L : Finset Ln) :
    (anchorConfigurations R P L).card =
      ∑ l ∈ L, (orderedTriples (P.filter fun p => R p l)).card *
        (P.filter fun p => ¬ R p l).card := let _ := instDecidableEqLn; by
  classical
  simp only [anchorConfigurations, Finset.card_sigma, Finset.card_product]

theorem sum_card_anchorConfigurations_neighbors (R : Pt → Ln → Prop)
    (P : Finset Pt) (L : Finset Ln) :
    (∑ x ∈ P, (anchorConfigurations R (joinedNeighbors R P L x) L).card) =
      ∑ c ∈ anchorConfigurations R P L, (anchorWitnesses R P L c).card := by
  classical
  have heq (x : Pt) : anchorConfigurations R (joinedNeighbors R P L x) L =
      (anchorConfigurations R P L).filter (fun c =>
        c.2.1.1 ∈ joinedNeighbors R P L x ∧
        c.2.1.2.1 ∈ joinedNeighbors R P L x ∧
        c.2.1.2.2 ∈ joinedNeighbors R P L x ∧
        c.2.2 ∈ joinedNeighbors R P L x) := by
    ext c
    have hsub : joinedNeighbors R P L x ⊆ P := Finset.filter_subset _ _
    simp only [mem_anchorConfigurations, Finset.mem_filter]
    constructor
    · rintro ⟨hl, h1, h2, h3, h4, hrest⟩
      exact ⟨⟨hl, hsub h1, hsub h2, hsub h3, hsub h4, hrest⟩, h1, h2, h3, h4⟩
    · rintro ⟨⟨hl, _, _, _, _, hrest⟩, h1, h2, h3, h4⟩
      exact ⟨hl, h1, h2, h3, h4, hrest⟩
  simp_rw [heq, anchorWitnesses, Finset.card_filter]
  exact Finset.sum_comm

end RyserCoveringCounterexample.Incidence

end

end OAI
