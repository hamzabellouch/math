import Mathlib
import OAI.Computability.VertexCover.Fourier.SourceOccurrences

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                        
section

namespace UniqueGames.Foundations.Hastad.SourceHonest

open UniqueGames.Reduction.CloneGap
open UniqueGames.Reduction.FiniteNoise
open scoped BigOperators

def taggedAssignment {V C I J : Type} (left : V → I) (right : C → J) :
    (V × Cube I) ⊕ ((C × Cube J) ⊕ Unit) → Bool
  | .inl (v, f) => f (left v)
  | .inr (.inl («c», g)) => g (right «c»)
  | .inr (.inr _) => false

@[simp] theorem taggedAssignment_left {V C I J : Type}
    (left : V → I) (right : C → J) (v : V) (f : Cube I) :
    taggedAssignment left right (.inl (v, f)) = f (left v) := rfl

@[simp] theorem taggedAssignment_right {V C I J : Type}
    (left : V → I) (right : C → J) («c» : C) (g : Cube J) :
    taggedAssignment left right (.inr (.inl («c», g))) = g (right «c») := rfl

theorem taggedAssignment_right_restriction {V C I J : Type}
    (left : V → I) (right : C → J) («c» : C) (valid : J → Bool)
    (honest : {j : J // valid j = true}) (hright : right «c» = honest.val)
    (extend : Cube {j : J // valid j = true} → Cube J)
    (hextend : ∀ (g : Cube {j : J // valid j = true})
      (j : {j : J // valid j = true}), extend g j.val = g j)
    (j₀ : {j : J // valid j = true}) (h : HalfCube j₀) :
    taggedAssignment left right (.inr (.inl («c», extend h.val))) = h.val honest := by
  change extend h.val (right «c») = h.val honest
  rw [hright]
  exact hextend h.val honest

section Local

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

end Local

section NumberedStorage

open SourceOccurrences

variable {V C I J : Type}

theorem numbered_assignment_restriction
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (left : V → I) (right : C → J) (v : V) («c» : C)
    (valid : J → Bool) (i₀ : I) (j₀ j : {j : J // valid j = true})
    (hright : right «c» = j.val) :
    assignmentOfKey vE cE iE jE (taggedAssignment left right) ∘
      localAddress vE cE iE jE v «c» valid i₀ j₀ =
      FoldedEquation.storedAssignment (fun h => h.val (left v)) (fun h => h.val j) := by
  funext a
  cases a with
  | inl h =>
    simp only [Function.comp_apply, localAddress, assignmentOfKey_code,
      taggedAssignment_left, FoldedEquation.storedAssignment, Sum.elim_inl]
  | inr h =>
    simp only [Function.comp_apply, localAddress, assignmentOfKey_code,
      taggedAssignment_right, hright, extendRestricted_valid,
      FoldedEquation.storedAssignment, Sum.elim_inr]

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in

theorem conditionedOccurrence_honest_satisfied
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (left : V → I) (right : C → J) (v : V) («c» : C)
    (valid : J → Bool) (π : J → I) (i₀ : I)
    (j₀ j : {j : J // valid j = true})
    (hright : right «c» = j.val) (hπ : π j.val = left v)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedOccurrence vE cE iE jE v «c» valid π i₀ j₀ f g μ)
      (assignmentOfKey vE cE iE jE (taggedAssignment left right)) = !(μ j.val) := by
  rw [conditionedOccurrence, satisfied_mapEquation,
    numbered_assignment_restriction vE cE iE jE left right v «c» valid i₀ j₀ j hright]
  exact conditioned_equation_honest_satisfied valid π i₀ (left v) j₀ j hπ f g μ

theorem conditionedOccurrenceList_honest_acceptance {D : ℕ} (positive : 0 < D)
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (left : V → I) (right : C → J) (v : V) («c» : C)
    (valid : J → Bool) (π : J → I) (i₀ : I)
    (j₀ j : {j : J // valid j = true})
    (hright : right «c» = j.val) (hπ : π j.val = left v)
    (tape : Encoding (SourceTape.TestTape I J D)) :
    let equations := occurrenceList tape (fun t =>
      conditionedOccurrence vE cE iE jE v «c» valid π i₀ j₀
        t.1 t.2.2 (realizedNoise t.2.1))
    ((equations.countP (fun e => satisfied e
      (assignmentOfKey vE cE iE jE (taggedAssignment left right)))) : ℝ) /
        equations.length = 1 - (D : ℝ)⁻¹ := by
  dsimp only
  rw [occurrenceList_acceptance]
  calc
    _ = SourceTape.tapeAcceptance D π (fun f => f (left v)) (fun g => g j.val) := by
      unfold SourceTape.tapeAcceptance
      apply Finset.expect_congr rfl
      intro t _
      rw [conditionedOccurrence_honest_satisfied vE cE iE jE left right v «c»
        valid π i₀ j₀ j hright hπ, dictator_test_parity π (left v) j.val hπ]
      cases realizedNoise t.2.1 j.val <;> rfl
    _ = _ := by
      rw [SourceTape.tapeAcceptance_eq_realizedTestAcceptance]
      exact realizedTestAcceptance_dictator positive π (left v) j.val hπ

end NumberedStorage

section Source

open SourceContexts
open SourceOccurrences

def honestGlobal (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) :
    (VariableContext F u × Cube (I u)) ⊕
      ((ClauseContext F u × Cube (J u)) ⊕ Unit) → Bool :=
  taggedAssignment (fun v => honestI F v assignment) (fun «c» => honestJ F «c» assignment)

def honestBits (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) : Fin (nBits F u) → Bool :=
  assignmentOfKey (variableEncoding F u) (clauseEncoding F u) (iEncoding u)
    (jEncoding u) (honestGlobal F u assignment)

@[simp] theorem honestBits_code (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool)
    (key : GlobalKey (VariableContext F u) (ClauseContext F u) (I u) (J u)) :
    honestBits F u assignment ((proofEncoding F u).code key) =
      honestGlobal F u assignment key :=
  assignmentOfKey_code (variableEncoding F u) (clauseEncoding F u)
    (iEncoding u) (jEncoding u) (honestGlobal F u assignment) key

@[simp] theorem honestBits_dummy (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) :
    honestBits F u assignment (dummyIndex F u) = false := by
  rw [dummyIndex, honestBits_code]
  rfl

def honestValidJ (F : Target.Formula) {u : ℕ} («c» : ClauseContext F u)
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    {j : J u // validJ F «c» j = true} :=
  ⟨honestJ F «c» assignment, honestJ_valid F «c» assignment hs⟩

theorem validJ_nonempty_of_satisfying (F : Target.Formula) {u : ℕ}
    («c» : ClauseContext F u) (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    Nonempty {j : J u // validJ F «c» j = true} :=
  ⟨honestValidJ F «c» assignment hs⟩

theorem leftResponse_honest (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) (v : VariableContext F u) :
    leftResponse F u (honestBits F u assignment) v =
      fun f => f (honestI F v assignment) := by
  funext f
  simp only [leftResponse, honestBits_code, honestGlobal, taggedAssignment,
    foldedAnswer_dictator]

theorem rightResponse_honest (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true)
    («c» : ClauseContext F u) :
    rightResponse F u (honestBits F u assignment) «c» =
      fun g => g (honestJ F «c» assignment) := by
  funext g
  cases ha : rightAnchor F «c» with
  | none =>
    have hf := (rightAnchor_none_iff F «c»).mp ha (honestJ F «c» assignment)
    rw [honestJ_valid F «c» assignment hs] at hf
    cases hf
  | some j₀ =>
    simp only [rightResponse, ha, honestBits_code, honestGlobal, taggedAssignment]
    have ht : (fun h : HalfCube j₀ =>
        extendRestricted (validJ F «c») h.val (honestJ F «c» assignment)) =
        fun h => h.val (honestValidJ F «c» assignment hs) := by
      funext h
      exact extendRestricted_valid (validJ F «c») h.val (honestValidJ F «c» assignment hs)
    rw [ht]
    exact conditionedFoldedAnswer_dictator (validJ F «c») j₀
      (honestValidJ F «c» assignment hs) g

theorem context_tapeAcceptance {D : ℕ} (positive : 0 < D)
    (F : Target.Formula) {u : ℕ} («c» : ClauseContext F u) (s : SlotContext u)
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true)
    (i₀ : I u) (j₀ : {j : J u // validJ F «c» j = true}) :
    SourceTape.tapeAcceptance D (pi F «c» (sampledVariables F «c» s))
      (foldedAnswer i₀ (fun h => h.val (honestI F (sampledVariables F «c» s) assignment)))
      (conditionedFoldedAnswer (validJ F «c») j₀
        (fun h => h.val (honestValidJ F «c» assignment hs))) =
      1 - (D : ℝ)⁻¹ := by
  exact tapeAcceptance_conditioned_dictators positive (validJ F «c»)
    (pi F «c» (sampledVariables F «c» s)) i₀ _ j₀ _
    (pi_honest_sampled F «c» s assignment)

theorem sourceEquation_honest_satisfied (F : Target.Formula) (u D : ℕ)
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true)
    (p : SourceIndex F u D) :
    satisfied (sourceEquation F u D p) (honestBits F u assignment) =
      !(realizedNoise p.2.2.1 (honestJ F p.1.1 assignment)) := by
  simp only [sourceEquation, contextEquation_satisfied, leftResponse_honest,
    rightResponse_honest F u assignment hs]
  rw [dictator_test_parity _ _ _ (pi_honest_sampled F p.1.1 p.1.2 assignment)]

theorem rawSourceList_honest_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (hF : F.clauses ≠ [])
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    ((rawSourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (rawSourceList F u D).length = 1 - (D : ℝ)⁻¹ := by
  have hc : 0 < F.clauses.length := List.length_pos_iff.mpr hF
  let : Nonempty (Fin F.clauses.length) := ⟨⟨0, hc⟩⟩
  rw [rawSourceList_acceptance F u D hD]
  have heq («c» : ClauseContext F u) (s : SlotContext u) :
      testAcceptance ((D : ℝ)⁻¹) (pi F «c» (sampledVariables F «c» s))
        (leftResponse F u (honestBits F u assignment) (sampledVariables F «c» s))
        (rightResponse F u (honestBits F u assignment) «c») = 1 - (D : ℝ)⁻¹ := by
    rw [leftResponse_honest, rightResponse_honest F u assignment hs]
    exact testAcceptance_dictator _ _ _ _ (pi_honest_sampled F «c» s assignment)
  simp_rw [heq]
  simp only [Fintype.expect_const]

theorem sourceList_honest_acceptance_nonempty (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (hF : F.clauses ≠ [])
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (sourceList F u D).length = 1 - (D : ℝ)⁻¹ := by
  rw [sourceList_nonempty F u D hF]
  exact rawSourceList_honest_acceptance F u D hD hF assignment hs

theorem sourceList_honest_acceptance (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    1 - (D : ℝ)⁻¹ ≤ ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℝ) /
        (sourceList F u D).length := by
  by_cases hF : F.clauses = []
  · rw [sourceList_empty F u D hF]
    simp only [List.countP_cons, List.countP_nil, emptyFormulaEquation_satisfied,
      honestBits_dummy, Bool.not_false, ↓reduceIte,
      Nat.zero_add, Nat.cast_one, List.length_cons, List.length_nil, div_one]
    exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg D))
  · exact (sourceList_honest_acceptance_nonempty F u D hD hF assignment hs).ge

theorem sourceList_honest_acceptance_rat (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    1 - (D : ℚ)⁻¹ ≤ ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℚ) /
        (sourceList F u D).length := by
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast, Rat.cast_div] using
    sourceList_honest_acceptance F u D hD assignment hs

theorem sourceList_honest_acceptance_nonempty_rat (F : Target.Formula) (u D : ℕ)
    (hD : 0 < D) (hF : F.clauses ≠ [])
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    ((sourceList F u D).countP
      (fun e => satisfied e (honestBits F u assignment)) : ℚ) /
        (sourceList F u D).length = 1 - (D : ℚ)⁻¹ := by
  apply Rat.cast_injective (α := ℝ)
  simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast, Rat.cast_div] using
    sourceList_honest_acceptance_nonempty F u D hD hF assignment hs

end Source

end UniqueGames.Foundations.Hastad.SourceHonest

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
