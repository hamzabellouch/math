import OAI.Computability.PerfectCompleteness.Construction.CanonicalLocalCompletion
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalVertexNames
import OAI.Computability.PerfectCompleteness.Foundations.OccurrenceStochasticLemmas

namespace OAI


namespace PerfectCompleteness.CanonicalNamedGame

open CanonicalGame CanonicalKeys
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {v m n : Nat} {E I B : Type*} {V : I → Type*}
  [DecidableEq I] [∀ i, AddCommGroup (V i)]
  [∀ i, Module DirectionQuotient.F2 (V i)]
  {clauses : Fin m → SourceClause.NormalizedClause v}
  (F : BlockFamily clauses n E I V B)
  (occurrences : List E) (coverage : ∀ e, e ∈ occurrences)

def leftKeys : List (Key n) := occurrences.map (leftKey F)

def rightKeys : List (Key n) := occurrences.map (rightKey F)

omit [DecidableEq I] in
@[simp] theorem leftKeys_length : (leftKeys F occurrences).length = occurrences.length := by
  simp only [leftKeys, List.length_map]

@[simp] theorem rightKeys_length : (rightKeys F occurrences).length = occurrences.length := by
  simp only [rightKeys, List.length_map]

omit [DecidableEq I] in
include coverage in
theorem left_mem (x : LeftVertex F) : x.val ∈ leftKeys F occurrences := by
  obtain ⟨e, he⟩ := x.property
  exact List.mem_map.mpr ⟨e, coverage e, he⟩

include coverage in
theorem right_mem (y : RightVertex F) : y.val ∈ rightKeys F occurrences := by
  obtain ⟨e, he⟩ := y.property
  exact List.mem_map.mpr ⟨e, coverage e, he⟩

def leftEmbedding : LeftVertex F ↪ Fin occurrences.length where
  toFun x :=
    let named := CanonicalVertexNames.name (leftKeys F occurrences) x.val
      (left_mem F occurrences coverage x)
    ⟨named.val, by simpa only [leftKeys_length] using named.isLt⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    apply (CanonicalVertexNames.name_eq_iff (leftKeys F occurrences) x.val y.val
      (left_mem F occurrences coverage x) (left_mem F occurrences coverage y)).mp
    apply Fin.ext
    exact congrArg (fun i : Fin occurrences.length => i.val) h

def rightEmbedding : RightVertex F ↪ Fin occurrences.length where
  toFun y :=
    let named := CanonicalVertexNames.name (rightKeys F occurrences) y.val
      (right_mem F occurrences coverage y)
    ⟨named.val, by simpa only [rightKeys_length] using named.isLt⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    apply (CanonicalVertexNames.name_eq_iff (rightKeys F occurrences) x.val y.val
      (right_mem F occurrences coverage x) (right_mem F occurrences coverage y)).mp
    apply Fin.ext
    exact congrArg (fun i : Fin occurrences.length => i.val) h

omit [DecidableEq I] in
@[simp] theorem leftEmbedding_at_val (e : E) :
    (leftEmbedding F occurrences coverage (leftAt F e)).val =
      (BinaryNameSearch.payloads (CanonicalVertexNames.tokens (leftKeys F occurrences))).idxOf
        (CanonicalVertexNames.payload (leftKey F e)) := rfl

@[simp] theorem rightEmbedding_at_val (e : E) :
    (rightEmbedding F occurrences coverage (rightAt F e)).val =
      (BinaryNameSearch.payloads (CanonicalVertexNames.tokens (rightKeys F occurrences))).idxOf
        (CanonicalVertexNames.payload (rightKey F e)) := rfl

omit [DecidableEq I] in
theorem leftEmbedding_at_eq_iff (e e' : E) :
    leftEmbedding F occurrences coverage (leftAt F e) =
      leftEmbedding F occurrences coverage (leftAt F e') ↔ leftKey F e = leftKey F e' := by
  constructor
  · intro h
    exact congrArg Subtype.val ((leftEmbedding F occurrences coverage).injective h)
  · intro h
    exact congrArg (leftEmbedding F occurrences coverage) (Subtype.ext h)

theorem rightEmbedding_at_eq_iff (e e' : E) :
    rightEmbedding F occurrences coverage (rightAt F e) =
      rightEmbedding F occurrences coverage (rightAt F e') ↔ rightKey F e = rightKey F e' := by
  constructor
  · intro h
    exact congrArg Subtype.val ((rightEmbedding F occurrences coverage).injective h)
  · intro h
    exact congrArg (rightEmbedding F occurrences coverage) (Subtype.ext h)

section CommonAlphabet

variable {E' A₁ A₂ : Type*} [Fintype E']
  [Fintype (LeftVertex F)] [Fintype (RightVertex F)] [Fintype A₁] [Fintype A₂]

def rename (G : OccurrenceGame E' (LeftVertex F) (RightVertex F) A₁ A₂) :
    OccurrenceGame E' (Fin occurrences.length) (Fin occurrences.length) A₁ A₂ :=
  OccurrenceVertexEmbedding.rename G
    (leftEmbedding F occurrences coverage) (rightEmbedding F occurrences coverage)

@[simp] theorem rename_occurrences
    (G : OccurrenceGame E' (LeftVertex F) (RightVertex F) A₁ A₂) :
    (rename F occurrences coverage G).occurrences = G.occurrences := rfl

@[simp] theorem rename_accepts
    (G : OccurrenceGame E' (LeftVertex F) (RightVertex F) A₁ A₂) :
    (rename F occurrences coverage G).accepts = G.accepts := rfl

theorem rename_value_eq [Nonempty A₁] [Nonempty A₂]
    (G : OccurrenceGame E' (LeftVertex F) (RightVertex F) A₁ A₂) :
    (rename F occurrences coverage G).value = G.value :=
  OccurrenceVertexEmbedding.value_eq G
    (leftEmbedding F occurrences coverage) (rightEmbedding F occurrences coverage)

end CommonAlphabet


variable [Finite I] [∀ i, Finite (V i)] [Finite B]
  [Fintype E] [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ x, Fintype (LeftLabel F x)] [∀ y, Fintype (RightLabel F y)]

local instance rightAlphabet_nonempty (δ : ℚ) :
    Nonempty (Fin (CanonicalLocalCompletion.alphabet n δ)) :=
  ⟨⟨0, CanonicalLocalCompletion.alphabet_positive n δ⟩⟩

local instance leftAlphabet_nonempty (δ : ℚ) :
    Nonempty (Fin (2 * CanonicalLocalCompletion.alphabet n δ)) :=
  ⟨⟨0, Nat.mul_pos (by decide) (CanonicalLocalCompletion.alphabet_positive n δ)⟩⟩

def completed (μ : FiniteDistribution E) (δ : ℚ) :=
  rename F occurrences coverage (CanonicalLocalCompletion.family F μ δ).game

omit [∀ y, Fintype (RightLabel F y)] in
@[simp] theorem completed_left (μ : FiniteDistribution E) (δ : ℚ)
    (e : E) (seed : Fin ((CanonicalLocalCompletion.family F μ δ).size e)) :
    (completed F occurrences coverage μ δ).left ⟨e, seed⟩ =
      leftEmbedding F occurrences coverage (leftAt F e) := rfl

omit [∀ y, Fintype (RightLabel F y)] in
@[simp] theorem completed_right (μ : FiniteDistribution E) (δ : ℚ)
    (e : E) (seed : Fin ((CanonicalLocalCompletion.family F μ δ).size e)) :
    (completed F occurrences coverage μ δ).right ⟨e, seed⟩ =
      rightEmbedding F occurrences coverage (rightAt F e) := rfl

omit [∀ y, Fintype (RightLabel F y)] in
theorem completed_value_eq (μ : FiniteDistribution E) (δ : ℚ) :
    (completed F occurrences coverage μ δ).value =
      (CanonicalLocalCompletion.family F μ δ).game.value :=
  rename_value_eq F occurrences coverage _

theorem completed_value_le (μ : FiniteDistribution E) (δ : ℚ) (hδ : 0 < δ) :
    (completed F occurrences coverage μ δ).value ≤
      (CanonicalGame.game F μ).value + (δ : ℝ) / 3 := by
  rw [completed_value_eq]
  exact CanonicalLocalCompletion.family_value_le F μ δ hδ

theorem completed_value_of_satisfying (μ : FiniteDistribution E) (δ : ℚ)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    (completed F occurrences coverage μ δ).value = 1 := by
  rw [completed_value_eq]
  exact CanonicalLocalCompletion.family_value_of_satisfying F μ δ assignment hsat

end
end PerfectCompleteness.CanonicalNamedGame

end OAI
