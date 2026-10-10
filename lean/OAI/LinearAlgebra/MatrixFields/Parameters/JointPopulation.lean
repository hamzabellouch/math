import Mathlib
import OAI.LinearAlgebra.MatrixFields.Extraction.JointMaskedSelection
import OAI.LinearAlgebra.MatrixFields.Extraction.JointPairClassWindows

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointPopulation

open MatrixMultiplication.Foundation
open scoped BigOperators

attribute [local instance] Classical.propDecidable

structure HistoryKey where
  lot : ℕ
  initialShape : Fin 3 → ℕ
  physicalPlacement : Equiv.Perm (Fin 3)
  parentSplits : List ((Fin 3 → ℕ) × Bool)
  subdivisions : List ℕ

abbrev Shape := Fin 17 × Fin 17 × Fin 17

def shapeSide (s : Fin 3) (u : Shape) : Fin 17 :=
  if s = 0 then u.1 else if s = 1 then u.2.1 else u.2.2

variable {H : Type*} [Fintype H] [DecidableEq H]
    (counts : H → Shape → ℕ)

abbrev Positions (h : H) := Fin (∑ u, counts h u)
abbrev Target := ∀ h, ExactWords (counts h)

def canonicalTarget : Target counts :=
  fun h => Classical.choice (exactWords_nonempty (counts h))

theorem target_card : Fintype.card (Target counts) =
    ∏ h, Nat.multinomial Finset.univ (counts h) := by
  simp only [Target, Fintype.card_pi, exactWords_card]

omit [Fintype H] [DecidableEq H] in
theorem target_nonempty : Nonempty (Target counts) := ⟨canonicalTarget counts⟩

abbrev Position := Σ h, Positions counts h

def triple (e : Target counts) : JointCoarseHashing.Triple (Position counts) :=
  (fun p => (e p.1).val p.2 |>.1,
    fun p => (e p.1).val p.2 |>.2.1,
    fun p => (e p.1).val p.2 |>.2.2)

omit [Fintype H] [DecidableEq H] in
theorem triple_injective : Function.Injective (triple counts) := by
  intro e f h
  funext c
  apply Subtype.ext
  funext i
  apply Prod.ext
  · exact congrArg (fun t : JointCoarseHashing.Triple (Position counts) => t.1 ⟨c, i⟩) h
  · apply Prod.ext
    · exact congrArg (fun t : JointCoarseHashing.Triple (Position counts) => t.2.1 ⟨c, i⟩) h
    · exact congrArg (fun t : JointCoarseHashing.Triple (Position counts) => t.2.2 ⟨c, i⟩) h

def targetSet : Finset (JointCoarseHashing.Triple (Position counts)) :=
  Finset.univ.image (triple counts)

theorem targetSet_card : (targetSet counts).card =
    ∏ h, Nat.multinomial Finset.univ (counts h) := by
  rw [targetSet, Finset.card_image_of_injective _ (triple_injective counts)]
  simpa using target_card counts

abbrev Class (e : Target counts) (h : H) (u : Shape) :=
  {i : Positions counts h // (e h).val i = u}

omit [Fintype H] [DecidableEq H] in
theorem class_card (e : Target counts) (h : H) (u : Shape) :
    Fintype.card (Class counts e h u) = counts h u := (e h).property u

omit [Fintype H] [DecidableEq H] in
theorem symbol_count_pos (e : Target counts) (h : H) (i : Positions counts h) :
    0 < counts h ((e h).val i) := by
  rw [← class_card counts e h ((e h).val i)]
  exact Fintype.card_pos_iff.mpr ⟨⟨i, rfl⟩⟩

omit [Fintype H] [DecidableEq H] in
theorem triple_support (sum : H → ℕ)
    (hsupport : ∀ h u, 0 < counts h u →
      u.1.val + u.2.1.val + u.2.2.val = sum h) (e : Target counts) :
    JointCoarseHashing.HasSupportSum (fun p : Position counts => sum p.1) (triple counts e) := by
  intro p
  exact hsupport p.1 ((e p.1).val p.2) (symbol_count_pos counts e p.1 p.2)

omit [Fintype H] [DecidableEq H] in
theorem exists_position_permutation (e f : Target counts) :
    ∃ p : ∀ h, Equiv.Perm (Positions counts h), ∀ h, (e h).val ∘ p h = (f h).val := by
  have hp : ∀ h, ∃ p : Equiv.Perm (Positions counts h), (e h).val ∘ p = (f h).val := by
    intro h
    apply (samePopulation_iff_permutation _ _).mp
    intro u
    rw [(e h).property, (f h).property]
  choose p hp using hp
  exact ⟨p, hp⟩

def sideWord (s : Fin 3) (t : JointCoarseHashing.Triple (Position counts))
    (h : H) : Positions counts h → Fin 17 :=
  fun i => shapeSide s (t.1 ⟨h, i⟩, t.2.1 ⟨h, i⟩, t.2.2 ⟨h, i⟩)

omit [Fintype H] [DecidableEq H] in
theorem sideWord_triple (s : Fin 3) (e : Target counts) (h : H) :
    sideWord counts s (triple counts e) h = shapeSide s ∘ (e h).val := rfl

omit [Fintype H] [DecidableEq H] in
theorem marginal_population_eq (e f : Target counts) (h : H) (s : Fin 3) (a : Fin 17) :
    wordPopulation (sideWord counts s (triple counts e) h) a =
      wordPopulation (sideWord counts s (triple counts f) h) a := by
  obtain ⟨p, hp⟩ := exists_position_permutation counts e f
  rw [sideWord_triple, sideWord_triple, ← hp h]
  exact (wordPopulation_reindex (shapeSide s ∘ (e h).val) (p h) a).symm

def ambientSet (sum : H → ℕ) : Finset (JointCoarseHashing.Triple (Position counts)) :=
  Finset.univ.filter fun t =>
    JointCoarseHashing.HasSupportSum (fun p : Position counts => sum p.1) t ∧
    ∀ h s a, wordPopulation (sideWord counts s t h) a =
      wordPopulation (sideWord counts s (triple counts (canonicalTarget counts)) h) a

theorem targetSet_subset_ambient (sum : H → ℕ)
    (hsupport : ∀ h u, 0 < counts h u →
      u.1.val + u.2.1.val + u.2.2.val = sum h) :
    targetSet counts ⊆ ambientSet counts sum := by
  intro t ht
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, triple_support counts sum hsupport e, ?_⟩
  intro h s a
  exact marginal_population_eq counts e (canonicalTarget counts) h s a

end MatrixMultiplication.JointPopulation

end
end

end MatrixAllFields

end OAI
