import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases

namespace OAI

/-! A finite set-partition expansion, presented by explicit surjective block
labels. This separates the finite combinatorics from complex matrix moments. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace MUB6.EqualityPatterns

variable {A P B V : Type*}

/-- Each `label p` is a surjection onto the blocks of one partition. -/
structure Family (A P : Type*) where
  blocks : P → ℕ
  label : (p : P) → A → Fin (blocks p)
  onto : ∀ p, Function.Surjective (label p)
  unique : ∀ p q, (∀ i j, label p i = label p j ↔ label q i = label q j) → p = q

namespace Family

def flatten (F : Family A P) (s : Σ p, Fin (F.blocks p) ↪ B) : A → B :=
  fun i => s.2 (F.label s.1 i)

theorem flatten_injective (F : Family A P) : Function.Injective (F.flatten (B := B)) := by
  rintro ⟨p, e⟩ ⟨q, f⟩ h
  have hpq : p = q := F.unique p q (by
    intro i j
    have hi := congrFun h i
    have hj := congrFun h j
    change e (F.label p i) = f (F.label q i) at hi
    change e (F.label p j) = f (F.label q j) at hj
    constructor
    · intro hij
      apply f.injective
      rw [← hi, ← hj, hij]
    · intro hij
      apply e.injective
      rw [hi, hj, hij])
  subst q
  congr 1
  ext b
  obtain ⟨i, rfl⟩ := F.onto p b
  exact congrFun h i

theorem flatten_surjective (F : Family A P)
    (cover : ∀ f : A → B, ∃ p, ∀ i j,
      F.label p i = F.label p j ↔ f i = f j) :
    Function.Surjective (F.flatten (B := B)) := by
  classical
  intro f
  obtain ⟨p, hp⟩ := cover f
  let r : Fin (F.blocks p) → A := Function.surjInv (F.onto p)
  have hr : ∀ b, F.label p (r b) = b := Function.rightInverse_surjInv (F.onto p)
  let e : Fin (F.blocks p) ↪ B :=
    ⟨fun b => f (r b), by
      intro b c h
      have hbc := (hp (r b) (r c)).mpr h
      simpa only [hr] using hbc⟩
  refine ⟨⟨p, e⟩, ?_⟩
  funext i
  exact (hp (r (F.label p i)) i).mp (hr _)

/-- Every function has exactly one equality pattern and an injection assigning
distinct values to its blocks. No probabilistic premise is used. -/
def assignmentsEquiv (F : Family A P)
    (cover : ∀ f : A → B, ∃ p, ∀ i j,
      F.label p i = F.label p j ↔ f i = f j) :
    (Σ p, Fin (F.blocks p) ↪ B) ≃ (A → B) :=
  Equiv.ofBijective F.flatten ⟨F.flatten_injective, F.flatten_surjective cover⟩

theorem sum_assignments [Fintype A] [Fintype P] [Fintype B] [AddCommMonoid V]
    (F : Family A P)
    (cover : ∀ f : A → B, ∃ p, ∀ i j,
      F.label p i = F.label p j ↔ f i = f j) (value : (A → B) → V) :
    (∑ f : A → B, value f) =
      ∑ p, ∑ e : Fin (F.blocks p) ↪ B, value (fun i => e (F.label p i)) := by
  classical
  have h := (F.assignmentsEquiv cover).sum_comp value
  change (∑ s : Σ p, Fin (F.blocks p) ↪ B, value (F.flatten s)) =
    (∑ f : A → B, value f) at h
  rw [Fintype.sum_sigma] at h
  exact h.symm

end Family

end MUB6.EqualityPatterns

end

end OAI
