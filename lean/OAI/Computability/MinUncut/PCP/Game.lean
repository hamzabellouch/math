import Mathlib
import OAI.Computability.MinUncut.PCP.Occurrences
import OAI.Computability.MinUncut.Encoding.GameDecoder
import OAI.Computability.MinUncut.Games.Reindexing

namespace OAI

noncomputable section
namespace MinUncutGames.Foundations.Hastad.SourceGame

open scoped BigOperators
open Target PCP Games SourceContexts

theorem event_nonempty (F : Formula) (hne : F.clauses ≠ []) :
    Nonempty (RandomEvent F) :=
  ⟨(⟨0, List.length_pos_iff.mpr hne⟩, .first)⟩

def eventLaw (F : Formula) (hne : F.clauses ≠ []) :
    FiniteDistribution (RandomEvent F) := by
  let : Nonempty (RandomEvent F) := event_nonempty F hne
  exact FiniteDistribution.uniform _

def visibleQuestion (F : Formula) (e : RandomEvent F) :
    Fin F.«variables» × Fin F.clauses.length :=
  (nameAt (clauseAt F e.1) e.2, e.1)

def baseGame (F : Formula) (hne : F.clauses ≠ []) :
    Game (Fin F.«variables») (Fin F.clauses.length) Bool ClauseAnswer where
  questions := (eventLaw F hne).pushforward (visibleQuestion F)
  accepts := baseAccepts F

@[simp] theorem baseGame_accepts (F : Formula) (hne : F.clauses ≠ [])
    (v : Fin F.«variables») (c : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    (baseGame F hne).accepts v c i j = baseAccepts F v c i j := rfl

theorem eventLaw_probability (F : Formula) (hne : F.clauses ≠ [])
    (P : RandomEvent F → Bool) :
    (eventLaw F hne).probability P =
      (∑ e : RandomEvent F, if P e then (1 : ℝ) else 0) /
        (3 * F.clauses.length : ℕ) := by
  classical
  simp only [eventLaw, FiniteDistribution.uniform, FiniteDistribution.probability]
  simp_rw [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  cases P e <;> simp [RandomEvent, Fintype.card_prod, card_slot, Nat.mul_comm]

theorem sum_slots (H : Slot → ℝ) :
    (∑ s : Slot, H s) = H .first + H .second + H .third := by
  have hu : (Finset.univ : Finset Slot) = {.first, .second, .third} := by
    ext s
    cases s <;> simp
  rw [hu]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_self, not_false_eq_true, Finset.sum_singleton]
  ring

theorem sum_slot_accepts (F : Formula) (alice : AliceStrategy F)
    (bob : BobStrategy F) (c : Fin F.clauses.length) :
    (∑ s : Slot, if accepts F alice bob (c,s) then (1 : ℝ) else 0) =
      (acceptedSlots (clauseAt F c) (alice c)
        (honestAnswer (clauseAt F c) bob) : ℕ) := by
  rw [sum_slots]
  by_cases hs : localSatisfies (clauseAt F c) (alice c) = true
  · by_cases h₁ : (alice c).first = bob (clauseAt F c)[0].variableIndex <;>
      by_cases h₂ : (alice c).second = bob (clauseAt F c)[1].variableIndex <;>
      by_cases h₃ : (alice c).third = bob (clauseAt F c)[2].variableIndex <;>
      norm_num [accepts, hs, acceptedSlots, matchingSlots, honestAnswer, answerAt, nameAt,
        h₁, h₂, h₃]
  · simp [accepts, acceptedSlots, hs]

theorem failureCount_eq_sum_map (F : Formula) (bob : BobStrategy F)
    (cs : List (Fin F.clauses.length)) :
    failureCount F bob cs =
      (cs.map (fun c => clauseFailure (clauseAt F c) bob)).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [failureCount, List.map_cons, List.sum_cons, ih]

theorem failureCount_allIndices (F : Formula) (bob : BobStrategy F) :
    failureCount F bob (allIndices F) =
      ∑ c : Fin F.clauses.length, clauseFailure (clauseAt F c) bob := by
  rw [failureCount_eq_sum_map]
  unfold allIndices
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

theorem verifier_probability_plus_failure (F : Formula) (hne : F.clauses ≠ [])
    (alice : AliceStrategy F) (bob : BobStrategy F) :
    (eventLaw F hne).probability (accepts F alice bob) +
      (failureCount F bob (allIndices F) : ℝ) / (3 * F.clauses.length : ℕ) ≤ 1 := by
  have hm : (0 : ℝ) < (3 * F.clauses.length : ℕ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 3) (List.length_pos_iff.mpr hne)
  have hlocal (c : Fin F.clauses.length) :
      (∑ s : Slot, if accepts F alice bob (c,s) then (1 : ℝ) else 0) +
        (clauseFailure (clauseAt F c) bob : ℝ) ≤ 3 := by
    rw [sum_slot_accepts]
    exact_mod_cast local_rejection_bound (clauseAt F c) (alice c) bob
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset _)) => hlocal c)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  rw [eventLaw_probability, failureCount_allIndices]
  push_cast
  push_cast at hm
  rw [Fintype.sum_prod_type, ← add_div]
  apply (div_le_one hm).mpr
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hsum

theorem base_success_le_verifier (F : Formula) (hne : F.clauses ≠ [])
    (strategy : Strategy (Fin F.«variables») (Fin F.clauses.length) Bool ClauseAnswer) :
    (baseGame F hne).success strategy ≤
      (eventLaw F hne).probability (accepts F strategy.2 strategy.1) := by
  unfold Game.success baseGame
  rw [FiniteDistribution.probability_pushforward]
  apply FiniteDistribution.probability_mono
  intro e he
  exact baseAccepts_implies_sampled F e.1 e.2 _ _ he

theorem base_value_le_of_clause_gap (F : Formula) (hne : F.clauses ≠ [])
    (δ : ℝ) (hgap : ∀ bob : BobStrategy F,
      δ * F.clauses.length ≤ (failureCount F bob (allIndices F) : ℝ)) :
    (baseGame F hne).value ≤ 1 - δ / 3 := by
  apply (Game.value_le_iff _ _).mpr
  intro strategy
  have hbase := base_success_le_verifier F hne strategy
  have hprob := verifier_probability_plus_failure F hne strategy.2 strategy.1
  have hm : (0 : ℝ) < F.clauses.length :=
    Nat.cast_pos.mpr (List.length_pos_iff.mpr hne)
  have hg : δ / 3 ≤ (failureCount F strategy.1 (allIndices F) : ℝ) /
      (3 * F.clauses.length : ℕ) := by
    have hden : (0 : ℝ) < (3 * F.clauses.length : ℕ) := by
      exact_mod_cast Nat.mul_pos (by decide : 0 < 3) (List.length_pos_iff.mpr hne)
    apply (le_div_iff₀ hden).mpr
    calc
      δ / 3 * (3 * F.clauses.length : ℕ) = δ * F.clauses.length := by push_cast; ring
      _ ≤ _ := hgap strategy.1
  linarith

theorem pushforward_comp {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (μ : FiniteDistribution X) (f : X → Y) (g : Y → Z) :
    (μ.pushforward f).pushforward g = μ.pushforward (g ∘ f) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  simp only [FiniteDistribution.pushforward]
  calc
    _ = ∑ y : Y, ∑ x : X, if f x = y then
        (if g y = z then μ.weight x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : g y = z <;> simp [h]
    _ = _ := by rw [Finset.sum_comm]; simp

theorem expectation_pushforward {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (f : X → Y) (H : Y → ℝ) :
    (μ.pushforward f).expectation H = μ.expectation (H ∘ f) := by
  classical
  simp only [FiniteDistribution.expectation, FiniteDistribution.pushforward,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

def repeatedVisible (F : Formula) (u : ℕ) (events : Fin u → RandomEvent F) :
    VariableContext F u × ClauseContext F u :=
  (fun t => nameAt (clauseAt F (events t).1) (events t).2,
   fun t => (events t).1)

theorem repeated_questions (F : Formula) (hne : F.clauses ≠ []) (u : ℕ) :
    ((baseGame F hne).repetition u).questions =
      ((eventLaw F hne).iid u).pushforward (repeatedVisible F u) := by
  change (((eventLaw F hne).pushforward (visibleQuestion F)).iid u).transport
    (Game.tupleQuestionEquiv u) = _
  rw [FiniteDistribution.iid_pushforward, ← FiniteDistribution.pushforward_equiv,
    pushforward_comp]
  rfl

theorem repeated_expectation (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (H : VariableContext F u × ClauseContext F u → ℝ) :
    ((baseGame F hne).repetition u).questions.expectation H =
      𝔼 events : Fin u → RandomEvent F, H (repeatedVisible F u events) := by
  let : Nonempty (RandomEvent F) := event_nonempty F hne
  rw [repeated_questions, expectation_pushforward]
  change ((FiniteDistribution.uniform (RandomEvent F)).iid u).expectation _ = _
  rw [FiniteDistribution.iid_uniform, FiniteDistribution.expectation_uniform,
    Fintype.expect_eq_sum_div_card]
  rfl

theorem repeated_expectation_split (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (H : VariableContext F u × ClauseContext F u → ℝ) :
    ((baseGame F hne).repetition u).questions.expectation H =
      𝔼 c : ClauseContext F u, 𝔼 s : SlotContext u,
        H (sampledVariables F c s, c) := by
  rw [repeated_expectation]
  calc
    _ = 𝔼 p : ClauseContext F u × SlotContext u,
        H (sampledVariables F p.1 p.2, p.1) :=
      Fintype.expect_equiv
        (Game.tupleQuestionEquiv (Q₁ := Fin F.clauses.length) (Q₂ := Slot) u)
        _ _ (fun _ => rfl)
    _ = _ := SourceTape.expect_prod _

def sourceProjectionGame (F : Formula) (hne : F.clauses ≠ []) (u : ℕ) :
    Game (VariableContext F u) (ClauseContext F u) (I u) (J u) :=
  projectionGame ((baseGame F hne).repetition u).questions
    (fun v c => pi F c v) (validJ F)

theorem projection_value_le_repetition (F : Formula) (hne : F.clauses ≠ [])
    (u : ℕ) :
    (sourceProjectionGame F hne u).value ≤ ((baseGame F hne).repetition u).value := by
  apply (Game.value_le_iff _ _).mpr
  intro strategy
  have h : (sourceProjectionGame F hne u).success strategy ≤
      ((baseGame F hne).repetition u).success strategy := by
    apply FiniteDistribution.probability_mono
    intro q hq
    have hlegal : pi F q.2 q.1 (strategy.2 q.2) = strategy.1 q.1 ∧
        validJ F q.2 (strategy.2 q.2) = true := by
      simpa only [Game.wins, sourceProjectionGame, projectionGame,
        decide_eq_true_eq] using hq
    apply (Game.repetition_accepts_iff _ _ _ _ _ _).mpr
    intro t
    exact projection_implies_coordinate_accepts F q.2 q.1
      (strategy.1 q.1) (strategy.2 q.2) hlegal.2 hlegal.1 t
  exact h.trans (Game.success_le_value _ strategy)

theorem source_acceptance_le (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (ε δ : ℝ) (i₀ : VariableContext F u → I u)
    (tableA : ∀ v, HalfCube (i₀ v) → Bool)
    (right : ∀ c : ClauseContext F u, ConditionedOracle (validJ F c))
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤ 4 * ε * δ ^ 2) :
    (𝔼 events : Fin u → RandomEvent F,
      questionAcceptance ε (fun v c => pi F c v)
        (fun v => foldedAnswer (i₀ v) (tableA v)) (fun c => (right c).answer)
        (repeatedVisible F u events)) ≤ (1 + δ) / 2 := by
  rw [← repeated_expectation F hne u]
  exact conditionedOracle_acceptance_bound _ ε δ _ (validJ F) i₀ tableA
    (fun _ => default) right hε hε' hδ
    ((projection_value_le_repetition F hne u).trans hvalue)

theorem source_acceptance_le_split (F : Formula) (hne : F.clauses ≠ []) (u : ℕ)
    (ε δ : ℝ) (i₀ : VariableContext F u → I u)
    (tableA : ∀ v, HalfCube (i₀ v) → Bool)
    (right : ∀ c : ClauseContext F u, ConditionedOracle (validJ F c))
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤ 4 * ε * δ ^ 2) :
    (𝔼 c : ClauseContext F u, 𝔼 s : SlotContext u,
      testAcceptance ε (pi F c (sampledVariables F c s))
        (foldedAnswer (i₀ (sampledVariables F c s)) (tableA (sampledVariables F c s)))
        (right c).answer) ≤ (1 + δ) / 2 := by
  have h := conditionedOracle_acceptance_bound
    ((baseGame F hne).repetition u).questions ε δ (fun v c => pi F c v)
    (validJ F) i₀ tableA (fun _ => default) right hε hε' hδ
    ((projection_value_le_repetition F hne u).trans hvalue)
  rw [repeated_expectation_split] at h
  exact h

end MinUncutGames.Foundations.Hastad.SourceGame

namespace MinUncutGames.Foundations.Hastad.SourceSoundness

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
    ((sourceList F u D).countP (fun e => MinUncutGames.Reduction.CloneGap.satisfied e bits) : ℝ) /
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
    ((sourceList F u D).countP (fun e => MinUncutGames.Reduction.CloneGap.satisfied e bits) : ℚ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  have h := sourceList_sound F hne u D hD hDtwo (δ : ℝ)
    (by exact_mod_cast hδ) hvalue bits
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact h

end MinUncutGames.Foundations.Hastad.SourceSoundness

end
namespace MinUncutGames.Foundations.Hastad.SourceHonest

open MinUncutGames.Reduction.CloneGap
open MinUncutGames.Reduction.FiniteNoise
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
    (left : V → I) (right : C → J) (v : V) (c : C)
    (valid : J → Bool) (i₀ : I) (j₀ j : {j : J // valid j = true})
    (hright : right c = j.val) :
    assignmentOfKey vE cE iE jE (taggedAssignment left right) ∘
      localAddress vE cE iE jE v c valid i₀ j₀ =
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
    (left : V → I) (right : C → J) (v : V) (c : C)
    (valid : J → Bool) (π : J → I) (i₀ : I)
    (j₀ j : {j : J // valid j = true})
    (hright : right c = j.val) (hπ : π j.val = left v)
    (f : Cube I) (g μ : Cube J) :
    satisfied (conditionedOccurrence vE cE iE jE v c valid π i₀ j₀ f g μ)
      (assignmentOfKey vE cE iE jE (taggedAssignment left right)) = !(μ j.val) := by
  rw [conditionedOccurrence, satisfied_mapEquation,
    numbered_assignment_restriction vE cE iE jE left right v c valid i₀ j₀ j hright]
  exact conditioned_equation_honest_satisfied valid π i₀ (left v) j₀ j hπ f g μ

theorem conditionedOccurrenceList_honest_acceptance {D : ℕ} (positive : 0 < D)
    (vE : Encoding V) (cE : Encoding C) (iE : Encoding I) (jE : Encoding J)
    (left : V → I) (right : C → J) (v : V) (c : C)
    (valid : J → Bool) (π : J → I) (i₀ : I)
    (j₀ j : {j : J // valid j = true})
    (hright : right c = j.val) (hπ : π j.val = left v)
    (tape : Encoding (SourceTape.TestTape I J D)) :
    let equations := occurrenceList tape (fun t =>
      conditionedOccurrence vE cE iE jE v c valid π i₀ j₀
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
      rw [conditionedOccurrence_honest_satisfied vE cE iE jE left right v c
        valid π i₀ j₀ j hright hπ, dictator_test_parity π (left v) j.val hπ]
      cases realizedNoise t.2.1 j.val <;> rfl
    _ = _ := by
      rw [SourceTape.tapeAcceptance_eq_realizedTestAcceptance]
      exact realizedTestAcceptance_dictator positive π (left v) j.val hπ

end NumberedStorage


open SourceContexts
open SourceOccurrences

def honestGlobal (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) :
    (VariableContext F u × Cube (I u)) ⊕
      ((ClauseContext F u × Cube (J u)) ⊕ Unit) → Bool :=
  taggedAssignment (fun v => honestI F v assignment) (fun c => honestJ F c assignment)

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

def honestValidJ (F : Target.Formula) {u : ℕ} (c : ClauseContext F u)
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    {j : J u // validJ F c j = true} :=
  ⟨honestJ F c assignment, honestJ_valid F c assignment hs⟩

theorem validJ_nonempty_of_satisfying (F : Target.Formula) {u : ℕ}
    (c : ClauseContext F u) (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true) :
    Nonempty {j : J u // validJ F c j = true} :=
  ⟨honestValidJ F c assignment hs⟩

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
    (c : ClauseContext F u) :
    rightResponse F u (honestBits F u assignment) c =
      fun g => g (honestJ F c assignment) := by
  funext g
  cases ha : rightAnchor F c with
  | none =>
    have hf := (rightAnchor_none_iff F c).mp ha (honestJ F c assignment)
    rw [honestJ_valid F c assignment hs] at hf
    cases hf
  | some j₀ =>
    simp only [rightResponse, ha, honestBits_code, honestGlobal, taggedAssignment]
    have ht : (fun h : HalfCube j₀ =>
        extendRestricted (validJ F c) h.val (honestJ F c assignment)) =
        fun h => h.val (honestValidJ F c assignment hs) := by
      funext h
      exact extendRestricted_valid (validJ F c) h.val (honestValidJ F c assignment hs)
    rw [ht]
    exact conditionedFoldedAnswer_dictator (validJ F c) j₀
      (honestValidJ F c assignment hs) g

theorem context_tapeAcceptance {D : ℕ} (positive : 0 < D)
    (F : Target.Formula) {u : ℕ} (c : ClauseContext F u) (s : SlotContext u)
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true)
    (i₀ : I u) (j₀ : {j : J u // validJ F c j = true}) :
    SourceTape.tapeAcceptance D (pi F c (sampledVariables F c s))
      (foldedAnswer i₀ (fun h => h.val (honestI F (sampledVariables F c s) assignment)))
      (conditionedFoldedAnswer (validJ F c) j₀
        (fun h => h.val (honestValidJ F c assignment hs))) =
      1 - (D : ℝ)⁻¹ := by
  exact tapeAcceptance_conditioned_dictators positive (validJ F c)
    (pi F c (sampledVariables F c s)) i₀ _ j₀ _
    (pi_honest_sampled F c s assignment)

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
  have heq (c : ClauseContext F u) (s : SlotContext u) :
      testAcceptance ((D : ℝ)⁻¹) (pi F c (sampledVariables F c s))
        (leftResponse F u (honestBits F u assignment) (sampledVariables F c s))
        (rightResponse F u (honestBits F u assignment) c) = 1 - (D : ℝ)⁻¹ := by
    rw [leftResponse_honest, rightResponse_honest F u assignment hs]
    exact testAcceptance_dictator _ _ _ _ (pi_honest_sampled F c s assignment)
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


end MinUncutGames.Foundations.Hastad.SourceHonest

namespace MinUncutGames.Soundness.RepetitionUpper

def bernoulliAverage (p : Rat) : Nat → (Nat → Rat) → Rat
  | 0, f => f 0
  | n + 1, f =>
      (1 - p) * bernoulliAverage p n f +
        p * bernoulliAverage p n (fun k => f (k + 1))

theorem bernoulliAverage_scale (p c : Rat) (n : Nat) (f : Nat → Rat) :
    bernoulliAverage p n (fun k => c * f k) = c * bernoulliAverage p n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [bernoulliAverage, ih]
      grind

theorem bernoulliAverage_geometric (p a : Rat) (n : Nat) :
    bernoulliAverage p n (fun k => a ^ k) = (1 - p * (1 - a)) ^ n := by
  induction n with
  | zero => simp [bernoulliAverage]
  | succ n ih =>
      simp only [bernoulliAverage]
      have hs : (fun k : Nat => a ^ (k + 1)) = fun k => a * a ^ k := by
        funext k
        rw [Rat.pow_succ, Rat.mul_comm]
      rw [hs, bernoulliAverage_scale, ih, Rat.pow_succ]
      grind

theorem bernoulliAverage_mono (p : Rat) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (n : Nat) (f g : Nat → Rat) (h : ∀ k, f k ≤ g k) :
    bernoulliAverage p n f ≤ bernoulliAverage p n g := by
  induction n generalizing f g with
  | zero => exact h 0
  | succ n ih =>
      have hleft := ih f g h
      have hright := ih (fun k => f (k + 1)) (fun k => g (k + 1))
        (fun k => h (k + 1))
      have hnp : 0 ≤ 1 - p := by grind
      have hl := Rat.mul_le_mul_of_nonneg_left hleft hnp
      have hr := Rat.mul_le_mul_of_nonneg_left hright hp
      simp only [bernoulliAverage]
      grind

theorem success_le_geometric
    (p a success : Rat) (n : Nat) (conditionalSuccess : Nat → Rat)
    (hp : 0 ≤ p) (hp' : p ≤ 1)
    (conditional : ∀ k, conditionalSuccess k ≤ a ^ k)
    (averaged : success ≤ bernoulliAverage p n conditionalSuccess) :
    success ≤ (1 - p * (1 - a)) ^ n := by
  have h := bernoulliAverage_mono p hp hp' n conditionalSuccess
    (fun k => a ^ k) conditional
  rw [bernoulliAverage_geometric] at h
  exact Rat.le_trans averaged h

theorem pow_mono_nonneg (x y : Rat) (hx : 0 ≤ x) (hxy : x ≤ y) (n : Nat) :
    x ^ n ≤ y ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hy : 0 ≤ y := Rat.le_trans hx hxy
      have hp : 0 ≤ x ^ n := Rat.pow_nonneg hx
      have h₁ := Rat.mul_le_mul_of_nonneg_left hxy hp
      have h₂ := Rat.mul_le_mul_of_nonneg_right ih hy
      simp only [Rat.pow_succ]
      exact Rat.le_trans h₁ h₂

def zeroProbability (d : Nat) : Rat := (1 / 2 : Rat) ^ d

theorem zeroProbability_nonneg (d : Nat) : 0 ≤ zeroProbability d := by
  exact Rat.pow_nonneg (by grind)

theorem zeroProbability_le_one (d : Nat) : zeroProbability d ≤ 1 := by
  induction d with
  | zero => simp [zeroProbability]
  | succ d ih =>
      have hp := zeroProbability_nonneg d
      simp only [zeroProbability, Rat.pow_succ] at *
      grind

theorem zeroProbability_antitone (d L : Nat) (hd : d ≤ L) :
    zeroProbability L ≤ zeroProbability d := by
  induction L with
  | zero =>
      have : d = 0 := by omega
      subst d
      exact Rat.le_refl
  | succ L ih =>
      by_cases heq : d = L + 1
      · subst d
        exact Rat.le_refl
      · have hdL : d ≤ L := by omega
        have h := ih hdL
        have hp := zeroProbability_nonneg L
        have hs : zeroProbability (L + 1) ≤ zeroProbability L := by
          simp only [zeroProbability, Rat.pow_succ] at *
          grind
        exact Rat.le_trans hs h

theorem geometric_le_dimension_bound (d L n : Nat) (hd : d ≤ L)
    (a : Rat) (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (1 - zeroProbability d * (1 - a)) ^ n ≤
      (1 - zeroProbability L * (1 - a)) ^ n := by
  have hp := zeroProbability_nonneg d
  have hp' := zeroProbability_le_one d
  have hdL := zeroProbability_antitone d L hd
  have hna : 0 ≤ 1 - a := by grind
  have hprod := Rat.mul_le_mul_of_nonneg_right hdL hna
  have hnprod := Rat.mul_le_mul_of_nonneg_right hp' hna
  apply pow_mono_nonneg
  · grind
  · grind

theorem projection_upper_bound
    (d L n : Nat) (hd : d ≤ L) (a success : Rat)
    (ha : 0 ≤ a) (ha' : a ≤ 1) (conditionalSuccess : Nat → Rat)
    (conditional : ∀ k, conditionalSuccess k ≤ a ^ k)
    (averaged : success ≤ bernoulliAverage (zeroProbability d) n conditionalSuccess) :
    success ≤ (1 - zeroProbability L * (1 - a)) ^ n := by
  have hs := success_le_geometric (zeroProbability d) a success n
    conditionalSuccess (zeroProbability_nonneg d) (zeroProbability_le_one d)
    conditional averaged
  exact Rat.le_trans hs (geometric_le_dimension_bound d L n hd a ha ha')

def decoderThreshold (theta : Rat) (q : Nat) : Rat := theta ^ 3 / (64 * (q : Rat))

theorem decoderThreshold_pos (theta : Rat) (q : Nat)
    (htheta : 0 < theta) (hq : 0 < q) : 0 < decoderThreshold theta q := by
  have hq' : (0 : Rat) < (q : Rat) := Rat.natCast_pos.mpr hq
  have ht := Rat.pow_pos (n := 3) htheta
  have hd : (0 : Rat) < 64 * (q : Rat) := by grind
  unfold decoderThreshold
  apply (Rat.lt_div_iff hd).mpr
  simpa using ht

theorem exists_pos_nat_gt (x : Rat) : ∃ n : Nat, 0 < n ∧ x < (n : Rat) := by
  refine ⟨x.ceil.toNat + 1, by omega, ?_⟩
  have hceil := Rat.le_ceil (x := x)
  have hint : x.ceil ≤ (x.ceil.toNat : Int) := by omega
  have hcast := Rat.intCast_le_intCast.mpr hint
  simp only [Rat.intCast_natCast] at hcast
  rw [Rat.natCast_add, Rat.natCast_ofNat]
  grind

theorem power_mul_growth_le_one (b : Rat) (hb : 0 ≤ b) (hb' : b ≤ 1)
    (n : Nat) : b ^ n * (1 + (n : Rat) * (1 - b)) ≤ 1 := by
  induction n with
  | zero =>
      simp only [Rat.pow_zero, Rat.natCast_ofNat, Rat.zero_mul, Rat.add_zero, Rat.one_mul]
      exact Rat.le_refl
  | succ n ih =>
      have hn := Rat.natCast_nonneg (a := n)
      have hc : 0 ≤ 1 - b := by grind
      have hnc : 0 ≤ ((n : Rat) + 1) * (1 - b) :=
        Rat.mul_nonneg (by grind) hc
      have hscaled := Rat.mul_le_mul_of_nonneg_right hb' hnc
      have hstep : b * (1 + ((n : Rat) + 1) * (1 - b)) ≤
          1 + (n : Rat) * (1 - b) := by grind
      have hprod := Rat.mul_le_mul_of_nonneg_left hstep (Rat.pow_nonneg (n := n) hb)
      simp only [Rat.pow_succ, Rat.natCast_add, Rat.natCast_ofNat]
      grind

theorem exists_power_lt (b threshold : Rat) (hb : 0 ≤ b) (hb' : b < 1)
    (ht : 0 < threshold) : ∃ n : Nat, 0 < n ∧ b ^ n < threshold := by
  have hc : 0 < 1 - b := by grind
  have hden : 0 < threshold * (1 - b) := Rat.mul_pos ht hc
  obtain ⟨n, hn, hlarge⟩ := exists_pos_nat_gt (1 / (threshold * (1 - b)))
  refine ⟨n, hn, ?_⟩
  have hlarge' := (Rat.div_lt_iff hden).mp hlarge
  have hn' := Rat.natCast_nonneg (a := n)
  have hg : 0 ≤ 1 + (n : Rat) * (1 - b) := by
    have h := Rat.mul_nonneg hn' (Rat.le_of_lt hc)
    grind
  have hbnd := power_mul_growth_le_one b hb (Rat.le_of_lt hb') n
  apply Rat.not_le.mp
  intro hbad
  have hmul := Rat.mul_le_mul_of_nonneg_right hbad hg
  grind

theorem zeroProbability_pos (d : Nat) : 0 < zeroProbability d := by
  exact Rat.pow_pos (by grind)

theorem exists_repetition_length (L q : Nat) (a theta : Rat)
    (ha : 0 ≤ a) (ha' : a < 1) (htheta : 0 < theta) (hq : 0 < q) :
    ∃ t : Nat, 0 < t ∧
      (1 - zeroProbability L * (1 - a)) ^ t < decoderThreshold theta q := by
  have hp := zeroProbability_pos L
  have hp' := zeroProbability_le_one L
  have hc : 0 < 1 - a := by grind
  have hmul := Rat.mul_le_mul_of_nonneg_right hp' (Rat.le_of_lt hc)
  have hpos := Rat.mul_pos hp hc
  apply exists_power_lt
  · grind
  · grind
  · exact decoderThreshold_pos theta q htheta hq

theorem soundness_of_bounds
    {Labeling Strategy : Type} (acceptance : Labeling → Rat)
    (success : Strategy → Rat) (delta lower upperBound : Rat)
    (extraction : ∀ labeling, delta < acceptance labeling →
      ∃ strategy, lower ≤ success strategy)
    (upper : ∀ strategy, success strategy ≤ upperBound)
    (gap : upperBound < lower) :
    ∀ labeling, acceptance labeling ≤ delta := by
  intro labeling
  apply Rat.not_lt.mp
  intro hbad
  obtain ⟨strategy, hlow⟩ := extraction labeling hbad
  have h : lower ≤ upperBound := Rat.le_trans hlow (upper strategy)
  exact (Rat.not_lt.mpr h) gap

theorem soundness_from_repetition
    {Labeling Strategy : Type} (acceptance : Labeling → Rat)
    (success : Strategy → Rat) (dimension : Strategy → Nat)
    (conditionalSuccess : Strategy → Nat → Rat)
    (delta a theta : Rat) (q L t : Nat) (ha : 0 ≤ a) (ha' : a ≤ 1)
    (dimension_le : ∀ strategy, dimension strategy ≤ L)
    (conditional : ∀ strategy k, conditionalSuccess strategy k ≤ a ^ k)
    (averaged : ∀ strategy, success strategy ≤
      bernoulliAverage (zeroProbability (dimension strategy)) t
        (conditionalSuccess strategy))
    (extraction : ∀ labeling, delta < acceptance labeling →
      ∃ strategy, decoderThreshold theta q ≤ success strategy)
    (gap : (1 - zeroProbability L * (1 - a)) ^ t < decoderThreshold theta q) :
    ∀ labeling, acceptance labeling ≤ delta := by
  apply soundness_of_bounds acceptance success delta (decoderThreshold theta q)
    ((1 - zeroProbability L * (1 - a)) ^ t) extraction
  · intro strategy
    exact projection_upper_bound (dimension strategy) L t (dimension_le strategy)
      a (success strategy) ha ha' (conditionalSuccess strategy)
      (conditional strategy) (averaged strategy)
  · exact gap

end MinUncutGames.Soundness.RepetitionUpper

end OAI
