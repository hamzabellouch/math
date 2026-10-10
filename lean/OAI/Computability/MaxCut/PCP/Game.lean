import Mathlib
import OAI.Computability.MaxCut.PCP.Occurrences
import OAI.Computability.MaxCut.Games.RowErasureSliceQuotient
import OAI.Computability.MaxCut.Encoding.GameDecoder
import OAI.Computability.MaxCut.Games.Reindexing

namespace OAI

noncomputable section
namespace MaxCutGames.Foundations.Hastad.SourceGame

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

/-- The local three-slot rejection inequality controls the actual uniform
incidence law, including repeated variable names and repeated clauses. -/
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

/-- A concrete clause-count gap supplies the base-game value bound. -/
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

/-- This identifies the repeated game law with the actual uniformly sampled
incidence tuples, retaining all collisions of their visible questions. -/
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

/-- The concrete constructor enumerates clause tuples and slot tuples as
separate lexicographic factors; this is exactly the same question law. -/
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

/-- The projection game has exactly the repeated question law, and its
legal right answers satisfy every coordinate of the original game. -/
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

end MaxCutGames.Foundations.Hastad.SourceGame

/-! The actual numbered equation list has exactly the acceptance bounded by
the private Fourier decoder. Only the repeated base-game value is an input
here; list semantics and all finite sampling laws are supplied. -/
namespace MaxCutGames.Foundations.Hastad.SourceSoundness

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

/-- Exact finite occurrence-list soundness, including arbitrary assignments
to unused padded proof bits and to the dummy bit. -/
theorem sourceList_sound (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℝ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * δ ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => MaxCutGames.Reduction.CloneGap.satisfied e bits) : ℝ) /
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

/-- The direct uniform reduction consumes rational occurrence fractions. -/
theorem sourceList_sound_rat (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℚ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * (δ : ℝ) ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => MaxCutGames.Reduction.CloneGap.satisfied e bits) : ℚ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  have h := sourceList_sound F hne u D hD hDtwo (δ : ℝ)
    (by exact_mod_cast hδ) hvalue bits
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact h

end MaxCutGames.Foundations.Hastad.SourceSoundness

end

namespace MaxCutGames.Foundations.Hastad.SourceHonest

open MaxCutGames.Reduction.CloneGap
open MaxCutGames.Reduction.FiniteNoise
open scoped BigOperators

/-- Padded query tables are evaluated at one coordinate per context. Left and
right tables have disjoint tags, and the unused dummy bit is fixed to false. -/
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

/-- Extending a conditioned half-table into padded ambient storage does not
change its honest bit. Only correctness on valid coordinates is required. -/
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
/-- Each honest emitted equation fails exactly when its selected noise bit is
true. This is a pointwise statement, before averaging any random tape. -/
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
/-- Local table equalities are enough to reuse the same assignment even when
different occurrences, contexts, or query positions name the same proof bit. -/
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

/-- The exact finite noise law gives honest acceptance for a conditioned right
table and an unconditioned left table, with arbitrary fixed folding bases. -/
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

/-- Numbering the global proof and then restricting it to one local table
recovers exactly the local honest half-tables. -/
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
/-- The globally numbered honest proof satisfies each actual occurrence
precisely when the corresponding noise bit is false. -/
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

/-- Exact normalized accepted count for the actual ordered random-tape list
at one incidence context. Equal equations remain separate occurrences. -/
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

/-- A single assignment to the globally tagged padded tables. It is defined
from the input assignment alone, before any incidence or test is sampled. -/
def honestGlobal (F : Target.Formula) (u : ℕ)
    (assignment : Fin F.«variables» → Bool) :
    (VariableContext F u × Cube (I u)) ⊕
      ((ClauseContext F u × Cube (J u)) ⊕ Unit) → Bool :=
  taggedAssignment (fun v => honestI F v assignment) (fun c => honestJ F c assignment)

/-- The same global proof in the construction's explicit radix numbering. -/
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

/-- Satisfiability supplies one consistent valid right coordinate in every
clause tuple, including tuples with repeated clauses or variable names. -/
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

/-- Actual sampled incidence contexts attain the same honest finite-noise
acceptance. Folding bases may be chosen independently of the assignment. -/
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

/-- The emitted equation, under the one global honest assignment, reads the
noise coordinate corresponding to the honest tuple of clause answers. -/
theorem sourceEquation_honest_satisfied (F : Target.Formula) (u D : ℕ)
    (assignment : Fin F.«variables» → Bool)
    (hs : ∀ clause ∈ F.clauses, clause.eval assignment = true)
    (p : SourceIndex F u D) :
    satisfied (sourceEquation F u D p) (honestBits F u assignment) =
      !(realizedNoise p.2.2.1 (honestJ F p.1.1 assignment)) := by
  simp only [sourceEquation, contextEquation_satisfied, leftResponse_honest,
    rightResponse_honest F u assignment hs]
  rw [dictator_test_parity _ _ _ (pi_honest_sampled F p.1.1 p.1.2 assignment)]

/-- Every actual occurrence is counted, even when its visible context,
equation, or one of its three addresses repeats. -/
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

/-- Rational acceptance form used by the finite reduction interface. -/
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

end MaxCutGames.Foundations.Hastad.SourceHonest

namespace MaxCutGames.Foundations.Repetition

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

@[simp] theorem logTwo_one : logTwo 1 = 0 := by simp [logTwo]

theorem logTwo_inv_le_of_half_pow_le {p : ℝ} (m : ℕ)
    (h : (1 / 2 : ℝ) ^ m ≤ p) : logTwo (1 / p) ≤ m := by
  have hp : 0 < p := (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m).trans_le h
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) m) h
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [Real.log_pow, hhalf] at hlog
  unfold logTwo
  rw [one_div, Real.log_inv]
  apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  nlinarith

/-- A nonzero step below the cutoff contracts by `(1+v)/2`. -/
theorem contraction_step {v ell : ℝ} {n m : ℕ} {p next : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hm : 1 ≤ m) (hmn : m < n) (hp : 0 ≤ p)
    (hmono : next ≤ p)
    (hprev : p ≤ ((1 + v) / 2) ^ m)
    (hcut : 2700 * (m : ℝ) * ell ≤ (1 - v) ^ 2 * ((n : ℝ) - m))
    (hstep : next ≤ p * (v + 15 * Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)))) :
    next ≤ ((1 + v) / 2) ^ (m + 1) := by
  by_cases hsmall : p ≤ ((1 + v) / 2) ^ (m + 1)
  · exact hmono.trans hsmall
  have hq : (1 / 2 : ℝ) ≤ (1 + v) / 2 := by linarith
  have hhalf : (1 / 2 : ℝ) ^ (m + 1) ≤ p :=
    (pow_le_pow_left₀ (by norm_num) hq (m + 1)).trans (le_of_not_ge hsmall)
  have hlog := logTwo_inv_le_of_half_pow_le (m + 1) hhalf
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < (n : ℝ) - m := by
    have hmnreal : (m : ℝ) < n := by exact_mod_cast hmn
    linarith
  have hmell : (m : ℝ) ≤ (m : ℝ) * ell := by nlinarith
  have hbudget : (m : ℝ) * ell + logTwo (1 / p) ≤ 3 * (m : ℝ) * ell := by
    simp only [Nat.cast_add, Nat.cast_one] at hlog
    nlinarith
  have hsqrt : Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)) ≤ (1 - v) / 30 := by
    apply (Real.sqrt_le_left (by linarith : 0 ≤ (1 - v) / 30)).2
    apply (div_le_iff₀ hden).2
    nlinarith
  have hfactor : v + 15 * Real.sqrt
      (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m)) ≤ (1 + v) / 2 := by
    linarith
  calc
    next ≤ p * (v + 15 * Real.sqrt
        (((m : ℝ) * ell + logTwo (1 / p)) / ((n : ℝ) - m))) := hstep
    _ ≤ p * ((1 + v) / 2) := mul_le_mul_of_nonneg_left hfactor hp
    _ ≤ ((1 + v) / 2) ^ m * ((1 + v) / 2) :=
      mul_le_mul_of_nonneg_right hprev (by linarith)
    _ = ((1 + v) / 2) ^ (m + 1) := (pow_succ _ _).symm

/-- The `m=0` case does not use the estimate `m+1 ≤ 2*m*ell`. -/
theorem initial_step {v ell next : ℝ} {n : ℕ}
    (hstep : next ≤ 1 * (v + 15 * Real.sqrt
      (((0 : ℝ) * ell + logTwo (1 / 1)) / ((n : ℝ) - 0)))) :
    next ≤ v := by simpa using hstep

/-- A real cutoff gives a valid step at every integer strictly below it. -/
theorem cutoff_step {v ell : ℝ} {n m : ℕ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hm : (m : ℝ) < (n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) :
    2700 * (m : ℝ) * ell ≤ (1 - v) ^ 2 * ((n : ℝ) - m) := by
  have hell0 : 0 < ell := by linarith
  have hd : (1 - v) ^ 2 ≤ 1 := by nlinarith
  have hmul : (m : ℝ) * (2925 * ell) < (n : ℝ) * (1 - v) ^ 2 :=
    (lt_div_iff₀ (by positivity : 0 < 2925 * ell)).1 hm
  have hdell : (1 - v) ^ 2 ≤ 225 * ell := by linarith
  have hprod := mul_le_mul_of_nonneg_left hdell (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  nlinarith

theorem cutoff_le_length {v ell : ℝ} (n : ℕ)
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell) :
    (n : ℝ) * (1 - v) ^ 2 / (2925 * ell) ≤ n := by
  have hell0 : 0 < ell := by linarith
  apply (div_le_iff₀ (by positivity : 0 < 2925 * ell)).2
  have hd : (1 - v) ^ 2 ≤ 2925 * ell := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The explicit recurrence obtained from a `15*sqrt` embedding error. -/
def ScalarRecurrence (p : ℕ → ℝ) (n : ℕ) (v ell : ℝ) : Prop :=
  ∀ m, m < n → p (m + 1) ≤ p m * (v + 15 * Real.sqrt
    (((m : ℝ) * ell + logTwo (1 / p m)) / ((n : ℝ) - m)))

/-- Induction to the ceiling of the real cutoff repairs the integer-rounding
omission in the printed scalar proof. -/
theorem decay_to_cutoff (p : ℕ → ℝ) (n : ℕ) {v ell : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hp0 : p 0 = 1) (hpnonneg : ∀ m, 0 ≤ p m)
    (hpmono : Antitone p) (hrec : ScalarRecurrence p n v ell) :
    p n ≤ ((1 + v) / 2) ^
      ((n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) := by
  let T : ℝ := (n : ℝ) * (1 - v) ^ 2 / (2925 * ell)
  let M : ℕ := Nat.ceil T
  have hMn : M ≤ n := Nat.ceil_le.mpr (cutoff_le_length n hv0 hv1 hell)
  have hind : ∀ m, m ≤ M → p m ≤ ((1 + v) / 2) ^ m := by
    intro m
    induction m with
    | zero => intro _; simp [hp0]
    | succ m ih =>
        intro hmM
        have hmM' : m < M := Nat.lt_of_succ_le hmM
        have hmn : m < n := hmM'.trans_le hMn
        have hprev := ih (Nat.le_of_lt hmM')
        by_cases hm0 : m = 0
        · subst m
          have hinit : p 1 ≤ v := by
            have hs := hrec 0 hmn
            simpa [hp0] using hs
          simpa using hinit.trans (by linarith : v ≤ (1 + v) / 2)
        · have hmT : (m : ℝ) < T := Nat.lt_ceil.mp hmM'
          exact contraction_step hv0 hv1 hell (Nat.one_le_iff_ne_zero.mpr hm0)
            hmn (hpnonneg m) (hpmono (Nat.le_succ m)) hprev
            (cutoff_step hv0 hv1 hell hmT) (hrec m hmn)
  have hq0 : 0 < (1 + v) / 2 := by linarith
  have hq1 : (1 + v) / 2 ≤ 1 := by linarith
  calc
    p n ≤ p M := hpmono hMn
    _ ≤ ((1 + v) / 2) ^ M := hind M le_rfl
    _ = ((1 + v) / 2) ^ (M : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ ((1 + v) / 2) ^ T :=
      Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (Nat.le_ceil T)

/-- The loss in one real-power block is cubic in the initial gap. -/
theorem block_contraction {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ((1 + v) / 2) ^ ((1 - v) ^ 2 / 2925 : ℝ) ≤
      1 - (1 - v) ^ 3 / 5850 := by
  have hd : (1 - v) ^ 2 ≤ 1 := by nlinarith
  have hb := rpow_one_add_le_one_add_mul_self
    (s := -(1 - v) / 2) (p := (1 - v) ^ 2 / 2925)
    (by linarith) (by positivity) (by nlinarith)
  have hbase : 1 + -(1 - v) / 2 = (1 + v) / 2 := by ring
  have hrhs : 1 + (1 - v) ^ 2 / 2925 * (-(1 - v) / 2) =
      1 - (1 - v) ^ 3 / 5850 := by ring
  rwa [hbase, hrhs] at hb

/-- Numerical endpoint of Holenstein's recurrence, with the published constant
6000. This theorem assumes only a concrete scalar recurrence, not any game
value bound. The derivation of that recurrence for games is separate. -/
theorem scalar_bound_6000 (p : ℕ → ℝ) (n : ℕ) {v ell : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (hell : 1 ≤ ell)
    (hp0 : p 0 = 1) (hpnonneg : ∀ m, 0 ≤ p m)
    (hpmono : Antitone p) (hrec : ScalarRecurrence p n v ell) :
    p n ≤ (1 - (1 - v) ^ 3 / 6000) ^ ((n : ℝ) / ell) := by
  have hell0 : 0 < ell := by linarith
  have hq0 : 0 ≤ (1 + v) / 2 := by linarith
  have hexp : 0 ≤ (n : ℝ) / ell := by positivity
  have hblock := block_contraction hv0 hv1
  have hweak : 1 - (1 - v) ^ 3 / 5850 ≤ 1 - (1 - v) ^ 3 / 6000 := by
    have : 0 ≤ (1 - v) ^ 3 := by positivity
    nlinarith
  calc
    p n ≤ ((1 + v) / 2) ^
        ((n : ℝ) * (1 - v) ^ 2 / (2925 * ell)) :=
      decay_to_cutoff p n hv0 hv1 hell hp0 hpnonneg hpmono hrec
    _ = (((1 + v) / 2) ^ ((1 - v) ^ 2 / 2925 : ℝ)) ^ ((n : ℝ) / ell) := by
      rw [← Real.rpow_mul hq0]
      congr 1
      ring
    _ ≤ (1 - (1 - v) ^ 3 / 6000) ^ ((n : ℝ) / ell) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hq0 _) (hblock.trans hweak) hexp

noncomputable def incidenceRate : ℝ := 1 - 1 / (100000 * 192 ^ 3)

theorem incidenceRate_pos : 0 < incidenceRate := by norm_num [incidenceRate]

theorem incidenceRate_lt_one : incidenceRate < 1 := by norm_num [incidenceRate]

/-- Exact rational arithmetic verifies the fourth-power comparison. -/
theorem incidenceRate_fourth :
    1 - (1 / 192 : ℝ) ^ 3 / 6000 ≤ incidenceRate ^ 4 := by
  norm_num [incidenceRate]

/-- Converting the real exponent `n/4` to an integral power loses only the
explicit slack already built into `incidenceRate`. -/
theorem incidence_rate_comparison (n : ℕ) :
    (1 - (1 / 192 : ℝ) ^ 3 / 6000) ^ ((n : ℝ) / 4) ≤ incidenceRate ^ n := by
  calc
    (1 - (1 / 192 : ℝ) ^ 3 / 6000) ^ ((n : ℝ) / 4)
        ≤ (incidenceRate ^ 4) ^ ((n : ℝ) / 4) :=
      Real.rpow_le_rpow (by norm_num) incidenceRate_fourth (by positivity)
    _ = incidenceRate ^ ((4 : ℝ) * ((n : ℝ) / 4)) :=
      (Real.rpow_natCast_mul incidenceRate_pos.le 4 ((n : ℝ) / 4)).symm
    _ = incidenceRate ^ (n : ℝ) := by congr 1; ring
    _ = incidenceRate ^ n := Real.rpow_natCast _ _

/-- The incidence-game rate follows from its concrete scalar recurrence.
The game-to-recurrence proof is deliberately not hidden in this statement. -/
theorem scalar_incidence_bound (p : ℕ → ℝ) (n : ℕ) {v : ℝ}
    (hv : v ≤ 1 - (1 / 192 : ℝ))
    (hp0 : p 0 = 1) (hpnonneg : ∀ m, 0 ≤ p m)
    (hpmono : Antitone p) (hrec : ScalarRecurrence p n v 4) :
    p n ≤ incidenceRate ^ n := by
  have hrec' : ScalarRecurrence p n (1 - (1 / 192 : ℝ)) 4 := by
    intro m hm
    exact (hrec m hm).trans (mul_le_mul_of_nonneg_left (by linarith) (hpnonneg m))
  have hbound := scalar_bound_6000 p n
    (v := 1 - (1 / 192 : ℝ)) (ell := 4)
    (by norm_num) (by norm_num) (by norm_num) hp0 hpnonneg hpmono hrec'
  norm_num only [sub_sub_cancel] at hbound
  have hcomparison := incidence_rate_comparison n
  norm_num at hcomparison
  exact hbound.trans hcomparison

end MaxCutGames.Foundations.Repetition

end OAI
