import Mathlib
import OAI.Combinatorics.IndependentSets.Fourier.Contexts
import OAI.Combinatorics.IndependentSets.Fourier.GameDecoder
import OAI.Combinatorics.IndependentSets.Machines.Tape
import OAI.Combinatorics.IndependentSets.Repetition.Reindexing

namespace OAI

noncomputable section
namespace IndependentSetsGames.Foundations.Hastad.SourceGame

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

end IndependentSetsGames.Foundations.Hastad.SourceGame

end

end OAI
