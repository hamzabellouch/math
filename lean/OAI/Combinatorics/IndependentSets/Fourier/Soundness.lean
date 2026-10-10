import Mathlib
import OAI.Combinatorics.IndependentSets.Fourier.Game
import OAI.Combinatorics.IndependentSets.Encoding.Concrete

namespace OAI

noncomputable section
namespace IndependentSetsGames.Foundations.Hastad.SourceSoundness

open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceGame

def leftTable (F : Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (v : VariableContext F u) : HalfCube (leftAnchor u) → Bool :=
  fun h => bits ((proofEncoding F u).code (.inl (v, h.val)))

def rightOracle (F : Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (c : ClauseContext F u) : ConditionedOracle (validJ F c) :=
  match h : rightAnchor F c with
  | none => .empty ((rightAnchor_none_iff F c).mp h)
  | some j₀ => .stored j₀
      (fun h => bits ((proofEncoding F u).code
        (.inr (.inl (c, extendRestricted (validJ F c) h.val)))))

@[simp] theorem rightOracle_answer (F : Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) (c : ClauseContext F u) :
    (rightOracle F u bits c).answer = rightResponse F u bits c := by
  unfold rightOracle
  split <;> simp_all [rightResponse, ConditionedOracle.answer]

@[simp] theorem leftTable_answer (F : Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) (v : VariableContext F u) :
    foldedAnswer (leftAnchor u) (leftTable F u bits v) = leftResponse F u bits v := rfl

theorem sourceList_sound (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℝ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * δ ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => IndependentSetsGames.Reduction.CloneGap.satisfied e bits) : ℝ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  rw [sourceList_nonempty F u D hne, rawSourceList_acceptance F u D hD]
  have hε : (0 : ℝ) < (D : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hD)
  have hε' : (D : ℝ)⁻¹ ≤ (1 : ℝ) / 2 := by
    have hd : (2 : ℝ) ≤ D := by exact_mod_cast hDtwo
    simpa only [one_div] using
      (inv_le_inv₀ (Nat.cast_pos.mpr hD) (by norm_num : (0 : ℝ) < 2)).mpr hd
  have h := source_acceptance_le_split F hne u ((D : ℝ)⁻¹) δ
    (fun _ => leftAnchor u) (leftTable F u bits) (rightOracle F u bits)
    hε hε' hδ hvalue
  simpa only [leftTable_answer, rightOracle_answer] using h

theorem sourceList_sound_rat (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℚ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * (δ : ℝ) ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => IndependentSetsGames.Reduction.CloneGap.satisfied e bits) : ℚ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  have h := sourceList_sound F hne u D hD hDtwo (δ : ℝ)
    (by exact_mod_cast hδ) hvalue bits
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact h

end IndependentSetsGames.Foundations.Hastad.SourceSoundness

end
namespace IndependentSetsGames.Foundations.Hastad.SourceHonest

open IndependentSetsGames.Reduction.CloneGap
open IndependentSetsGames.Reduction.FiniteNoise
open scoped BigOperators

def taggedAssignment {V C I J : Type} (left : V → I) (right : C → J) :
    (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit) → Bool
  | .inl (v, f) => f (left v)
  | .inr (.inl (c, g)) => g (right c)
  | .inr (.inr _) => false

@[simp] theorem taggedAssignment_left {V C I J : Type}
    (left : V → I) (right : C → J) (v : V) (f : Cube I) :
    taggedAssignment left right (.inl (v, f)) = f (left v) := rfl

@[simp] theorem taggedAssignment_right {V C I J : Type}
    (left : V → I) (right : C → J) (c : C) (g : Cube J) :
    taggedAssignment left right (.inr (.inl (c, g))) = g (right c) := rfl

theorem taggedAssignment_right_restriction {V C I J : Type}
    (left : V → I) (right : C → J) (c : C) (valid : J → Bool)
    (honest : {j : J // valid j = true}) (hright : right c = honest.val)
    (extend : Cube {j : J // valid j = true} → Cube J)
    (hextend : ∀ (g : Cube {j : J // valid j = true})
      (j : {j : J // valid j = true}), extend g j.val = g j)
    (j₀ : {j : J // valid j = true}) (h : HalfCube j₀) :
    taggedAssignment left right (.inr (.inl (c, extend h.val))) = h.val honest := by
  change extend h.val (right c) = h.val honest
  rw [hright]
  exact hextend h.val honest

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem conditioned_equation_honest_satisfied
    (valid : J → Bool) (π : J → I) (i₀ i : I)
    (j₀ j : {j : J // valid j = true}) (hπ : π j.val = i)
    (f : Cube I) (g μ : Cube J) :
    satisfied (FoldedEquation.conditionedEquation valid π i₀ j₀ f g μ)
        (FoldedEquation.storedAssignment (fun h => h.val i) (fun h => h.val j)) =
      !(μ j.val) := by
  rw [FoldedEquation.conditionedEquation_satisfied, foldedAnswer_dictator,
    conditionedFoldedAnswer_dictator, conditionedFoldedAnswer_dictator,
    dictator_test_parity π i j.val hπ]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem mapped_conditioned_equation_honest_satisfied {Name : Type}
    (valid : J → Bool) (π : J → I) (i₀ i : I)
    (j₀ j : {j : J // valid j = true}) (hπ : π j.val = i)
    (rename : FoldedEquation.Address i₀ j₀ → Name) (assignment : Name → Bool)
    (hleft : ∀ h, assignment (rename (.inl h)) = h.val i)
    (hright : ∀ h, assignment (rename (.inr h)) = h.val j)
    (f : Cube I) (g μ : Cube J) :
    satisfied (mapEquation rename
        (FoldedEquation.conditionedEquation valid π i₀ j₀ f g μ)) assignment =
      !(μ j.val) := by
  have hlocal : assignment ∘ rename =
      FoldedEquation.storedAssignment (fun h => h.val i) (fun h => h.val j) := by
    funext a
    cases a with
    | inl h => exact hleft h
    | inr h => exact hright h
  rw [satisfied_mapEquation, hlocal]
  exact conditioned_equation_honest_satisfied valid π i₀ i j₀ j hπ f g μ

theorem tapeAcceptance_conditioned_dictators {D : ℕ} (positive : 0 < D)
    (valid : J → Bool) (π : J → I) (i₀ i : I)
    (j₀ j : {j : J // valid j = true}) (hπ : π j.val = i) :
    SourceTape.tapeAcceptance D π
      (foldedAnswer i₀ (fun h => h.val i))
      (conditionedFoldedAnswer valid j₀ (fun h => h.val j)) =
        1 - (D : ℝ)⁻¹ := by
  rw [SourceTape.tapeAcceptance_eq_realizedTestAcceptance]
  exact realizedTestAcceptance_folded_conditioned_dictators positive π i₀ i valid j₀ j hπ

end IndependentSetsGames.Foundations.Hastad.SourceHonest

end OAI
