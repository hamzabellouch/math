import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternBulkIdentity
import OAI.NumberTheory.Ostmann.Construction.UnitPrimeCellSupport

namespace OAI

namespace Ostmann
open scoped Classical

noncomputable def primeBulkValues {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) : σ → ℕ :=
  Function.extend slot (fun j => (x j : ℕ)) base

@[simp] theorem primeBulkValues_at {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) (j : J) :
    primeBulkValues base slot x (slot j) = (x j : ℕ) := slot.injective.extend_apply _ _ j

theorem primeBulkValues_off {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) (i : σ) (hi : i ∉ Set.range slot) :
    primeBulkValues base slot x i = base i := Function.extend_apply' _ _ i hi

theorem primeBulkValues_prime {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P)
    (hP : ∀ p ∈ P, p.Prime) (hbase : ∀ i ∉ Set.range slot, (base i).Prime) :
    ∀ i, (primeBulkValues base slot x i).Prime := by
  intro i
  by_cases hi : i ∈ Set.range slot
  · obtain ⟨j, rfl⟩ := hi
    rw [primeBulkValues_at]
    exact hP _ (x j).property
  · rw [primeBulkValues_off base slot x i hi]
    exact hbase i hi

theorem primeBulkValues_injective_iff {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) :
    Function.Injective (primeBulkValues base slot x ∘ slot) ↔ Function.Injective x := by
  simp only [Function.comp_apply, primeBulkValues_at, Function.Injective]
  constructor
  · intro h i j hij
    exact h (congrArg Subtype.val hij)
  · intro h i j hij
    exact h (Subtype.ext hij)

/-- Removing each fixed nonbulk prime from the old cells enforces all cross
inequalities, while permitting equal bulk draws until their original gate. -/
theorem primeBulkValues_cross_of_deleted {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) (S deleted : J → Finset ℕ)
    (hx : ∀ j, (x j : ℕ) ∈ S j \ deleted j)
    (hdeleted : ∀ j i, i ∉ Set.range slot → base i ∈ deleted j) :
    ∀ i k, bulkIndexPredicate slot i ≠ bulkIndexPredicate slot k →
      primeBulkValues base slot x i ≠ primeBulkValues base slot x k := by
  have hc (j : J) (i : σ) (hi : i ∉ Set.range slot) :
      primeBulkValues base slot x (slot j) ≠ primeBulkValues base slot x i := by
    rw [primeBulkValues_at, primeBulkValues_off base slot x i hi]
    intro he
    exact (Finset.mem_sdiff.mp (hx j)).2 (he ▸ hdeleted j i hi)
  intro i k hik
  by_cases hi : i ∈ Set.range slot <;> by_cases hk : k ∈ Set.range slot
  · simp only [bulkIndexPredicate, hi, hk, decide_true, ne_eq, not_true_eq_false] at hik
  · obtain ⟨j, rfl⟩ := hi
    exact hc j k hk
  · obtain ⟨j, rfl⟩ := hk
    exact (hc j i hi).symm
  · simp only [bulkIndexPredicate, hi, hk, decide_false, ne_eq, not_true_eq_false] at hik

theorem primeBulkValues_outside_coprime {σ J : Type*} {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) (S deleted : J → Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hx : ∀ j, (x j : ℕ) ∈ S j \ deleted j)
    (outside : List ℕ) (hout : ∀ p ∈ outside, p.Prime)
    (hdeleted : ∀ j p, p ∈ outside → p ∈ deleted j) :
    ∀ j p, p ∈ outside → (primeBulkValues base slot x (slot j)).Coprime p := by
  intro j p hp
  rw [primeBulkValues_at]
  apply (Nat.coprime_primes (hP _ (x j).property) (hout p hp)).mpr
  intro he
  exact (Finset.mem_sdiff.mp (hx j)).2 (he ▸ hdeleted j p hp)

theorem primeBulkValues_cell_label {σ J Cell : Type*} [Fintype Cell] {P : Finset ℕ}
    (base : σ → ℕ) (slot : J ↪ σ) (x : J → P) (q : ℕ) [NeZero q]
    (u v : J → Cell → ℝ) (c₀ : Cell × (ZMod q)ˣ) (deleted : J → Finset ℕ)
    (hx : ∀ j, (x j : ℕ) ∈ primeCellSupport q
      (fun c : Cell × (ZMod q)ˣ => c.2.val.val) (fun c => u j c.1) (fun c => v j c.1) \ deleted j) :
    ∀ j, (primeBulkValues base slot x (slot j) : ZMod q) =
      ((primeCellLabel q (fun c : Cell × (ZMod q)ˣ => c.2.val.val)
        (fun c => u j c.1) (fun c => v j c.1) c₀ (x j)).2 : ZMod q) := by
  intro j
  rw [primeBulkValues_at]
  exact unitPrimeCellLabel_lift q (u j) (v j) c₀ (x j) (Finset.mem_sdiff.mp (hx j)).1

end Ostmann

end OAI
