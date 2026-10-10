import Mathlib
import OAI.Computability.DirectedFeedback.Machines.RuntimeSpace
import OAI.Computability.DirectedFeedback.Machines.MachineSubdivisionInit

namespace OAI


namespace DFVSGames.Explicit.MachineSubdivisionLoop

open Turing
open DFVSGames.Foundations DFVSGames.Foundations.Target
open DFVSGames.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame

theorem rowPayload_eq {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.rowPayload (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) = rowBits Q e edge := by
  rw [MachineSubdivisionBodySpec.rowPayload_eq _ _ _ _ _ (ready Q e edge edges emitted)
    (n + e) (n + Q + 2 * e) (n + Q + 2 * e + 1) rfl rfl rfl]
  simp only [MachineSubdivisionBodySpec.rowBits, rowBits, identityBits,
    MachineSubdivisionBody.tableBits, encodeWords_append, List.append_assoc]

theorem bodyResult_eq_frame {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.bodyResult (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) =
      frame Q (e + 1) edges (emitted ++ rowBits Q e edge) := by
  have indices := MachineSubdivisionBodySpec.result_indices
    (afterGuard Q e edge edges emitted) edge.source.val edge.target.val edge.permutation
    (bodyBits edges) (ready Q e edge edges emitted) n Q e rfl rfl rfl
  funext tape
  cases tape with
  | middle => exact indices.1
  | first => exact indices.2.1
  | last => exact indices.2.2
  | input => exact MachineSubdivisionBodySpec.result_input _ _ _ _ _ (ready Q e edge edges emitted)
  | accumulator =>
    rw [MachineSubdivisionBodySpec.result_accumulator _ _ _ _ _ (ready Q e edge edges emitted),
      rowPayload_eq]
    simp [afterGuard, frame, List.reverse_append]
  | _ =>
    rw [MachineSubdivisionBodySpec.bodyResult_eq _ _ _ _ _ (ready Q e edge edges emitted)]
    simp [MachineSubdivisionBodySpec.resultTapes, afterGuard, frame,
      MachineSubdivisionInit.resultTapes]

def bodyBound (n q Q : Nat) : Nat := 100 * (n + 3 * Q + q * (q + 1) + 1)

def bodyInTime {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) (he : e ≤ Q) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩
      (some ⟨some .guard, initialState, frame Q (e + 1) edges (emitted ++ rowBits Q e edge)⟩)
      (bodyBound n q Q) := by
  have run := MachineSubdivisionBody.bodyInTime (afterGuard Q e edge edges emitted)
    edge.source.val edge.target.val edge.permutation (bodyBits edges) (ready Q e edge edges emitted)
  rw [bodyResult_eq_frame] at run
  have bound := MachineSubdivisionBodySpec.bodyBudget_le (afterGuard Q e edge edges emitted)
    edge.source.val edge.target.val edge.permutation (bodyBits edges) (ready Q e edge edges emitted)
    n Q e edge.source.isLt edge.target.isLt he rfl rfl rfl
  exact { toEvalsTo := run.toEvalsTo, steps_le_m := run.steps_le_m.trans bound }

def loopInTime {n q : Nat} (Q e : Nat) (edges : List (Constraint n q))
    (emitted : List Bool) (fit : e + edges.length ≤ Q) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .guard, initialState, frame Q e edges emitted⟩
      (some ⟨some .finishStart, initialState,
        frame Q (e + edges.length) ([] : List (Constraint n q))
          (emitted ++ outputRows Q e edges)⟩)
      (edges.length * (bodyBound n q Q + 1) + 1) := by
  induction edges generalizing e emitted with
  | nil =>
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := by simp }
    change (machine q).step ⟨some .guard, initialState, frame Q e [] emitted⟩ = _
    simpa only [List.length_nil, Nat.add_zero, outputRows, List.append_nil]
      using guard_nil n q Q e emitted
  | cons edge edges ih =>
    have he : e ≤ Q := by simp only [List.length_cons] at fit; omega
    have remainingFit : (e + 1) + edges.length ≤ Q := by
      simp only [List.length_cons] at fit
      omega
    have guard : StateTransition.EvalsToInTime (machine q).step
        ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩
        (some ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩) 1 := {
      steps := 1
      evals_in_steps := by
        change (machine q).step
          ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩ = _
        exact guard_cons Q e edge edges emitted
      steps_le_m := Nat.le_refl _ }
    have body := bodyInTime Q e edge edges emitted he
    have tail := ih (e + 1) (emitted ++ rowBits Q e edge) remainingFit
    have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
    have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first tail
    have index_eq : (e + 1) + edges.length = e + (edge :: edges).length := by simp; omega
    have words_eq : (emitted ++ rowBits Q e edge) ++ outputRows Q (e + 1) edges =
        emitted ++ outputRows Q e (edge :: edges) := by
      simp only [outputRows, List.append_assoc]
    rw [index_eq, words_eq] at whole
    exact {
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega }

end DFVSGames.Explicit.MachineSubdivisionLoop


namespace DFVSGames.Explicit.MachineSubdivisionFinish

open Turing
open DFVSGames.Foundations.Complexity
open DFVSGames.Foundations.Hastad
open MachineSubdivisionProgram

noncomputable def timePolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q) clearKeys.length (prefixTime + 1)

theorem haltList_eq (q : Nat) (bits : List Bool) :
    haltList (machine q) bits =
      ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  cases k <;> simp [machine, SourceRuntimeFinish.canonicalTapes, Function.update]
  rfl

def finishStartInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (q := q)), initialState, base⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q .finishStart) initialState base) = _
    simp only [program, TM2.stepAux]
    rfl
  steps_le_m := Nat.le_refl _

theorem covers (k : Tape) (ha : k ≠ .accumulator) (ho : k ≠ .output) :
    k ∈ clearKeys := by
  rcases clearKeys_covers k with h | h | h
  · exact h
  · exact False.elim (ha h)
  · exact False.elim (ho h)

noncomputable def completePrefix (q : Nat) (input : List Bool) (prefixTime : Polynomial Nat)
    (base : Tape → List Bool)
    (execution : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨some .finishStart, initialState, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base .output = []) :
    TM2OutputsInTime (machine q) input (some (base .accumulator).reverse)
      ((timePolynomial q prefixTime).eval input.length) := by
  let bridge := finishStartInTime q base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (q := q)), initialState, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys covers
    ((), ()) (Label.finish (q := q)) none (program q) (fun _ => rfl)
    base outputEmpty ((), ()) none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (machine q)
    input (prefixTime + 1) prefixRun clearKeys Tape.accumulator Tape.output
    accumulator_not_mem_clearKeys output_not_mem_clearKeys covers base outputEmpty
    (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (machine q).step
    (initList (machine q) input)
    (some (haltList (machine q) (base .accumulator).reverse)) _
  rw [haltList_eq]
  exact run

end DFVSGames.Explicit.MachineSubdivisionFinish


namespace DFVSGames.Explicit

structure OccurrenceGame (V E A : Type*) where
  source : E → V
  target : E → V
  permutation : E → Equiv.Perm A

structure BipartiteGame (L R E A : Type*) where
  left : E → L
  right : E → R
  permutation : E → Equiv.Perm A
  simple : Function.Injective (fun e => (left e, right e))

namespace OccurrenceGame

def Satisfied {V E A : Type*} (G : OccurrenceGame V E A)
    (labeling : V → A) (e : E) : Prop :=
  labeling (G.target e) = G.permutation e (labeling (G.source e))

instance satisfiedDecidable {V E A : Type*} [DecidableEq A]
    (G : OccurrenceGame V E A) (labeling : V → A) (e : E) :
    Decidable (G.Satisfied labeling e) := inferInstanceAs (Decidable (_ = _))

def IsTranslation {V E A : Type*} [Add A] (G : OccurrenceGame V E A) : Prop :=
  ∃ offset : E → A, ∀ e a, G.permutation e a = a + offset e

end OccurrenceGame

namespace BipartiteGame

def Satisfied {L R E A : Type*} (G : BipartiteGame L R E A)
    (leftLabeling : L → A) (rightLabeling : R → A) (e : E) : Prop :=
  rightLabeling (G.right e) = G.permutation e (leftLabeling (G.left e))

instance satisfiedDecidable {L R E A : Type*} [DecidableEq A]
    (G : BipartiteGame L R E A) (a : L → A) (b : R → A) (e : E) :
    Decidable (G.Satisfied a b e) := inferInstanceAs (Decidable (_ = _))

def IsTranslation {L R E A : Type*} [Add A] (G : BipartiteGame L R E A) : Prop :=
  ∃ offset : E → A, ∀ e a, G.permutation e a = a + offset e

end BipartiteGame


open scoped BigOperators

namespace OccurrenceGame

variable {V E A : Type*} [Fintype E] [DecidableEq A]

def satisfiedCount (g : OccurrenceGame V E A) (a : V → A) : Nat :=
  ∑ e, if g.permutation e (a (g.source e)) = a (g.target e) then 1 else 0

theorem satisfiedCount_eq_sum_satisfied (g : OccurrenceGame V E A) (a : V → A) :
    satisfiedCount g a = ∑ e, if g.Satisfied a e then 1 else 0 := by
  classical
  unfold satisfiedCount
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : g.Satisfied a e
  · have h' : g.permutation e (a (g.source e)) = a (g.target e) := Eq.symm h
    rw [ite_eq_left h', ite_eq_left h]
  · have h' : ¬ g.permutation e (a (g.source e)) = a (g.target e) :=
      fun he => h he.symm
    rw [ite_eq_right h', ite_eq_right h]

variable [Fintype V] [Fintype A]

noncomputable def maxSatisfied (g : OccurrenceGame V E A) : Nat := by
  classical
  exact Finset.univ.sup (satisfiedCount g)

noncomputable def value (g : OccurrenceGame V E A) : ℝ :=
  (maxSatisfied g : ℝ) / Fintype.card E

theorem satisfiedCount_le_maxSatisfied (g : OccurrenceGame V E A) (a : V → A) :
    satisfiedCount g a ≤ maxSatisfied g := by
  classical
  exact Finset.le_sup (f := satisfiedCount g) (Finset.mem_univ a)

theorem maxSatisfied_attained [Nonempty A] (g : OccurrenceGame V E A) :
    ∃ a, satisfiedCount g a = maxSatisfied g := by
  classical
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (satisfiedCount g)
  exact ⟨a, ha.symm⟩

end OccurrenceGame

namespace BipartiteGame

variable {L R E A : Type*} [Fintype E] [DecidableEq A]

def satisfiedCount (g : BipartiteGame L R E A) (a : L → A) (b : R → A) : Nat :=
  ∑ e, if g.permutation e (a (g.left e)) = b (g.right e) then 1 else 0

theorem satisfiedCount_eq_sum_satisfied (g : BipartiteGame L R E A)
    (a : L → A) (b : R → A) :
    satisfiedCount g a b = ∑ e, if g.Satisfied a b e then 1 else 0 := by
  classical
  unfold satisfiedCount
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : g.Satisfied a b e
  · have h' : g.permutation e (a (g.left e)) = b (g.right e) := Eq.symm h
    rw [ite_eq_left h', ite_eq_left h]
  · have h' : ¬ g.permutation e (a (g.left e)) = b (g.right e) :=
      fun he => h he.symm
    rw [ite_eq_right h', ite_eq_right h]

variable [Fintype L] [Fintype R] [Fintype A]

noncomputable def maxSatisfied (g : BipartiteGame L R E A) : Nat := by
  classical
  exact Finset.univ.sup (fun ab : (L → A) × (R → A) => satisfiedCount g ab.1 ab.2)

noncomputable def value (g : BipartiteGame L R E A) : ℝ :=
  (maxSatisfied g : ℝ) / Fintype.card E

theorem satisfiedCount_le_maxSatisfied (g : BipartiteGame L R E A)
    (a : L → A) (b : R → A) : satisfiedCount g a b ≤ maxSatisfied g := by
  classical
  exact Finset.le_sup (f := fun ab : (L → A) × (R → A) => satisfiedCount g ab.1 ab.2)
    (Finset.mem_univ (a, b))

theorem maxSatisfied_attained [Nonempty A] (g : BipartiteGame L R E A) :
    ∃ a b, satisfiedCount g a b = maxSatisfied g := by
  classical
  obtain ⟨⟨a, b⟩, _, hab⟩ := Finset.exists_mem_eq_sup Finset.univ
    Finset.univ_nonempty
    (fun ab : (L → A) × (R → A) => satisfiedCount g ab.1 ab.2)
  exact ⟨a, b, hab.symm⟩

end BipartiteGame

namespace Subdivision

variable {V E A : Type*}

abbrev Left (V E : Type*) := V ⊕ E

abbrev Right (E : Type*) := E × Bool

abbrev Edge (E : Type*) := E × Fin 4

def left (g : OccurrenceGame V E A) (ei : Edge E) : Left V E :=
  if ei.2 = 0 then Sum.inl (g.source ei.1)
  else if ei.2 = 3 then Sum.inl (g.target ei.1)
  else Sum.inr ei.1

def right (ei : Edge E) : Right E := (ei.1, decide (2 ≤ ei.2.val))

def permutation (g : OccurrenceGame V E A) (ei : Edge E) : Equiv.Perm A :=
  if ei.2 = 3 then (g.permutation ei.1).symm else Equiv.refl A

theorem endpoints_injective (g : OccurrenceGame V E A) :
    Function.Injective (fun ei : Edge E => (left g ei, right ei)) := by
  rintro ⟨e, i⟩ ⟨f, j⟩ h
  have hef : e = f := congrArg (fun x => x.2.1) h
  subst f
  fin_cases i <;> fin_cases j <;> simp_all [left, right]

def game (g : OccurrenceGame V E A) :
    BipartiteGame (Left V E) (Right E) (Edge E) A where
  left := left g
  right := right
  permutation := permutation g
  simple := endpoints_injective g

theorem isTranslation [AddGroup A] (g : OccurrenceGame V E A)
    (hg : g.IsTranslation) : (game g).IsTranslation := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨fun ei => if ei.2 = 3 then -(c ei.1) else 0, ?_⟩
  intro ei a
  by_cases hi : ei.2 = 3
  · simp only [game, permutation, hi, ite_eq_left]
    apply (g.permutation ei.1).injective
    rw [(g.permutation ei.1).apply_symm_apply, hc]
    simp
  · simp [game, permutation, hi]

theorem binary_translation_offsets [AddGroup A]
    (hbinary : ∀ a : A, a + a = 0) (g : OccurrenceGame V E A)
    (c : E → A) (hc : ∀ e a, g.permutation e a = a + c e) :
    ∀ ei a, (game g).permutation ei a =
      a + (if ei.2 = 3 then c ei.1 else 0) := by
  intro ei a
  by_cases hi : ei.2 = 3
  · simp only [game, permutation, hi, ite_eq_left]
    apply (g.permutation ei.1).injective
    rw [(g.permutation ei.1).apply_symm_apply, hc, add_assoc, hbinary, add_zero]
  · simp [game, permutation, hi]

def restrict (a : Left V E → A) : V → A := fun v => a (Sum.inl v)

def extendLeft (g : OccurrenceGame V E A) (a : V → A) : Left V E → A :=
  Sum.elim a (fun e => a (g.source e))

def extendRight (g : OccurrenceGame V E A) (a : V → A) : Right E → A :=
  fun eb => a (g.source eb.1)

@[simp] theorem restrict_extendLeft (g : OccurrenceGame V E A) (a : V → A) :
    restrict (extendLeft g a) = a := rfl

theorem four_satisfied_implies_original (ρ : Equiv.Perm A) (u p q r v : A)
    (h₀ : u = p) (h₁ : q = p) (h₂ : q = r) (h₃ : ρ.symm v = r) :
    ρ u = v := by
  have h : u = r := h₀.trans (h₁.symm.trans h₂)
  rw [h, ← h₃, ρ.apply_symm_apply]

variable [DecidableEq A]

theorem local_count_le (ρ : Equiv.Perm A) (u p q r v : A) :
    (if u = p then 1 else 0) + (if q = p then 1 else 0) +
      (if q = r then 1 else 0) + (if ρ.symm v = r then 1 else 0) ≤
        3 + (if ρ u = v then 1 else 0 : Nat) := by
  by_cases h₀ : u = p <;> by_cases h₁ : q = p <;>
    by_cases h₂ : q = r <;> by_cases h₃ : ρ.symm v = r <;>
    by_cases h : ρ u = v <;> simp_all [Equiv.symm_apply_eq]

theorem local_count_extend (ρ : Equiv.Perm A) (u v : A) :
    (if u = u then 1 else 0) + (if u = u then 1 else 0) +
      (if u = u then 1 else 0) + (if ρ.symm v = u then 1 else 0) =
        3 + (if ρ u = v then 1 else 0 : Nat) := by
  by_cases h : ρ u = v
  · have h' : ρ.symm v = u := by rw [← h, ρ.symm_apply_apply]
    simp [h, h']
  · have h' : ρ.symm v ≠ u := by
      intro he
      apply h
      rw [← he, ρ.apply_symm_apply]
    simp [h, h']

theorem count_on_occurrence_le (g : OccurrenceGame V E A)
    (a : Left V E → A) (b : Right E → A) (e : E) :
    (∑ i : Fin 4, if (game g).permutation (e, i) (a ((game g).left (e, i))) =
        b ((game g).right (e, i)) then 1 else 0) ≤
      3 + (if g.permutation e (restrict a (g.source e)) =
        restrict a (g.target e) then 1 else 0 : Nat) := by
  rw [Fin.sum_univ_four]
  exact local_count_le (g.permutation e)
      (a (Sum.inl (g.source e))) (b (e, false)) (a (Sum.inr e))
      (b (e, true)) (a (Sum.inl (g.target e)))

theorem count_on_occurrence_extend (g : OccurrenceGame V E A) (a : V → A) (e : E) :
    (∑ i : Fin 4, if (game g).permutation (e, i)
      (extendLeft g a ((game g).left (e, i))) =
        extendRight g a ((game g).right (e, i)) then 1 else 0) =
      3 + (if g.permutation e (a (g.source e)) = a (g.target e) then 1 else 0 : Nat) := by
  rw [Fin.sum_univ_four]
  simpa [game, permutation, left, right, extendLeft, extendRight] using
    local_count_extend (g.permutation e) (a (g.source e)) (a (g.target e))

variable [Fintype E]

theorem satisfiedCount_le (g : OccurrenceGame V E A)
    (a : Left V E → A) (b : Right E → A) :
    (game g).satisfiedCount a b ≤
      3 * Fintype.card E + g.satisfiedCount (restrict a) := by
  unfold BipartiteGame.satisfiedCount OccurrenceGame.satisfiedCount
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ e, (3 + (if g.permutation e (restrict a (g.source e)) =
        restrict a (g.target e) then 1 else 0 : Nat)) :=
      Finset.sum_le_sum (fun e _ => count_on_occurrence_le g a b e)
    _ = _ := by simp [Finset.sum_add_distrib, Nat.mul_comm]

theorem satisfiedCount_extend (g : OccurrenceGame V E A) (a : V → A) :
    (game g).satisfiedCount (extendLeft g a) (extendRight g a) =
      3 * Fintype.card E + g.satisfiedCount a := by
  unfold BipartiteGame.satisfiedCount OccurrenceGame.satisfiedCount
  rw [Fintype.sum_prod_type]
  simp_rw [count_on_occurrence_extend]
  simp [Finset.sum_add_distrib, Nat.mul_comm]

@[simp] theorem edge_count : Fintype.card (Edge E) = 4 * Fintype.card E := by
  simp [Edge, Nat.mul_comm]

@[simp] theorem left_count [Fintype V] :
    Fintype.card (Left V E) = Fintype.card V + Fintype.card E := by
  simp [Left]

@[simp] theorem right_count : Fintype.card (Right E) = 2 * Fintype.card E := by
  simp [Right, Nat.mul_comm]

variable [Fintype V] [Fintype A] [Nonempty A]

theorem maxSatisfied_eq (g : OccurrenceGame V E A) :
    (game g).maxSatisfied = 3 * Fintype.card E + g.maxSatisfied := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro ab _
    exact (satisfiedCount_le g ab.1 ab.2).trans
      (Nat.add_le_add_left (g.satisfiedCount_le_maxSatisfied (restrict ab.1)) _)
  · obtain ⟨a, ha⟩ := g.maxSatisfied_attained
    rw [← ha, ← satisfiedCount_extend]
    exact BipartiteGame.satisfiedCount_le_maxSatisfied _ _ _

theorem value_eq [Nonempty E] (g : OccurrenceGame V E A) :
    (game g).value = 1 - (1 - g.value) / 4 := by
  have hE : (Fintype.card E : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [BipartiteGame.value, maxSatisfied_eq, edge_count, OccurrenceGame.value]
  push_cast
  field_simp [hE]
  ring

end Subdivision

end DFVSGames.Explicit


namespace DFVSGames.Foundations.PCP

open Target

structure ClauseAnswer where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq

inductive Slot where
  | first
  | second
  | third
  deriving DecidableEq

def answerAt (answer : ClauseAnswer) : Slot → Bool
  | .first => answer.first
  | .second => answer.second
  | .third => answer.third

def nameAt {n : Nat} (clause : Clause n) : Slot → Fin n
  | .first => clause[0].variableIndex
  | .second => clause[1].variableIndex
  | .third => clause[2].variableIndex

def literalValue (positive value : Bool) : Bool :=
  if positive then value else !value

def localSatisfies {n : Nat} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  (literalValue clause[0].positive answer.first ||
   literalValue clause[1].positive answer.second) ||
   literalValue clause[2].positive answer.third

def honestAnswer {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : ClauseAnswer :=
  ⟨assignment clause[0].variableIndex, assignment clause[1].variableIndex,
   assignment clause[2].variableIndex⟩

theorem honest_satisfies {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) :
    localSatisfies clause (honestAnswer clause assignment) = clause.eval assignment := rfl

theorem honest_answerAt {n : Nat} (clause : Clause n) (assignment : Fin n → Bool)
    (slot : Slot) : answerAt (honestAnswer clause assignment) slot =
      assignment (nameAt clause slot) := by
  cases slot <;> rfl

def matchingSlots (a b : ClauseAnswer) : Nat :=
  (if a.first = b.first then 1 else 0) +
  (if a.second = b.second then 1 else 0) +
  (if a.third = b.third then 1 else 0)

theorem matchingSlots_le (a b : ClauseAnswer) : matchingSlots a b ≤ 3 := by
  rcases a with ⟨a₁,a₂,a₃⟩
  rcases b with ⟨b₁,b₂,b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

theorem matchingSlots_eq_three (a b : ClauseAnswer) : matchingSlots a b = 3 ↔ a = b := by
  rcases a with ⟨a₁,a₂,a₃⟩
  rcases b with ⟨b₁,b₂,b₃⟩
  cases a₁ <;> cases a₂ <;> cases a₃ <;> cases b₁ <;> cases b₂ <;> cases b₃ <;> decide

def acceptedSlots {n : Nat} (clause : Clause n) (alice bob : ClauseAnswer) : Nat :=
  if localSatisfies clause alice then matchingSlots alice bob else 0

def clauseFailure {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Nat :=
  if clause.eval assignment then 0 else 1

theorem local_rejection_bound {n : Nat} (clause : Clause n) (alice : ClauseAnswer)
    (bob : Fin n → Bool) :
    acceptedSlots clause alice (honestAnswer clause bob) + clauseFailure clause bob ≤ 3 := by
  have hle := matchingSlots_le alice (honestAnswer clause bob)
  by_cases hb : clause.eval bob = true
  · simp only [clauseFailure, hb, ↓reduceIte, Nat.add_zero]
    unfold acceptedSlots
    split <;> omega
  · have hfailure : clauseFailure clause bob = 1 := by simp [clauseFailure, hb]
    rw [hfailure]
    by_cases ha : localSatisfies clause alice = true
    · have hne : alice ≠ honestAnswer clause bob := by
        intro h
        subst alice
        exact hb ((honest_satisfies clause bob).symm.trans ha)
      have hlt : matchingSlots alice (honestAnswer clause bob) ≠ 3 := by
        intro h
        exact hne ((matchingSlots_eq_three _ _).mp h)
      simp only [acceptedSlots, ha, ↓reduceIte]
      omega
    · simp [acceptedSlots, ha]

def clauseAt (formula : Formula) (index : Fin formula.clauses.length) :
    Clause formula.«variables» := formula.clauses[index.val]

abbrev RandomEvent (formula : Formula) := Fin formula.clauses.length × Slot
abbrev AliceStrategy (formula : Formula) := Fin formula.clauses.length → ClauseAnswer
abbrev BobStrategy (formula : Formula) := Fin formula.«variables» → Bool

def accepts (formula : Formula) (alice : AliceStrategy formula) (bob : BobStrategy formula)
    (event : RandomEvent formula) : Bool :=
  localSatisfies (clauseAt formula event.1) (alice event.1) &&
    decide (answerAt (alice event.1) event.2 = bob (nameAt (clauseAt formula event.1) event.2))

def acceptedCount (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) : List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => acceptedSlots (clauseAt formula i) (alice i)
      (honestAnswer (clauseAt formula i) bob) + acceptedCount formula alice bob rest

def failureCount (formula : Formula) (bob : BobStrategy formula) :
    List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => clauseFailure (clauseAt formula i) bob + failureCount formula bob rest

theorem total_rejection_bound (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) (indices : List (Fin formula.clauses.length)) :
    acceptedCount formula alice bob indices + failureCount formula bob indices ≤
      3 * indices.length := by
  induction indices with
  | nil => simp [acceptedCount, failureCount]
  | cons i rest ih =>
    have h := local_rejection_bound (clauseAt formula i) (alice i) bob
    simp only [acceptedCount, failureCount, List.length_cons]
    omega

def allIndices (formula : Formula) : List (Fin formula.clauses.length) :=
  List.finRange formula.clauses.length

theorem hastad_basic_verifier_soundness (formula : Formula) (a b : Nat)
    (sourceGap : ∀ bob : BobStrategy formula,
      a * formula.clauses.length ≤ b * failureCount formula bob (allIndices formula))
    (alice : AliceStrategy formula) (bob : BobStrategy formula) :
    b * acceptedCount formula alice bob (allIndices formula) + a * formula.clauses.length ≤
      b * (3 * formula.clauses.length) := by
  have ht := Nat.mul_le_mul_left b (total_rejection_bound formula alice bob (allIndices formula))
  have hg := sourceGap bob
  simp only [allIndices, List.length_finRange, Nat.mul_add] at *
  omega

theorem honest_accepts (formula : Formula) (assignment : BobStrategy formula)
    (satisfies : ∀ clause ∈ formula.clauses, clause.eval assignment = true)
    (event : RandomEvent formula) :
    accepts formula (fun i => honestAnswer (clauseAt formula i) assignment) assignment event = true := by
  have hc : (clauseAt formula event.1).eval assignment = true :=
    satisfies _ (List.getElem_mem _)
  simp [accepts, honest_satisfies, honest_answerAt, hc]

theorem verifier_completeness (formula : Formula) (sat : formula.Satisfiable) :
    ∃ (alice : AliceStrategy formula) (bob : BobStrategy formula),
      ∀ event : RandomEvent formula, accepts formula alice bob event = true := by
  rcases sat with ⟨assignment, hs⟩
  exact ⟨fun i => honestAnswer (clauseAt formula i) assignment, assignment,
    honest_accepts formula assignment hs⟩

abbrev LeftLabel (formula : Formula) (i : Fin formula.clauses.length) :=
  { answer : ClauseAnswer // localSatisfies (clauseAt formula i) answer = true }

def edgeProjection (formula : Formula) (event : RandomEvent formula)
    (label : LeftLabel formula event.1) : Bool := answerAt label.val event.2

theorem verifier_eq_projection (formula : Formula)
    (alice : ∀ i, LeftLabel formula i) (bob : BobStrategy formula) (event : RandomEvent formula) :
    accepts formula (fun i => (alice i).val) bob event =
      decide (edgeProjection formula event (alice event.1) =
        bob (nameAt (clauseAt formula event.1) event.2)) := by
  simp [accepts, (alice event.1).property, edgeProjection] ; rfl

def eventsAt (formula : Formula) (i : Fin formula.clauses.length) : List (RandomEvent formula) :=
  [(i, .first), (i, .second), (i, .third)]

def enumerateEvents (formula : Formula) : List (Fin formula.clauses.length) →
    List (RandomEvent formula)
  | [] => []
  | i :: rest => eventsAt formula i ++ enumerateEvents formula rest

theorem length_enumerateEvents (formula : Formula) (indices : List (Fin formula.clauses.length)) :
    (enumerateEvents formula indices).length = 3 * indices.length := by
  induction indices with
  | nil => simp [enumerateEvents]
  | cons i rest ih =>
    simp only [enumerateEvents, eventsAt, List.length_append, List.length_cons,
      List.length_nil, ih]
    omega

theorem accepted_eventsAt (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) (i : Fin formula.clauses.length) :
    ((eventsAt formula i).filter (accepts formula alice bob)).length =
      acceptedSlots (clauseAt formula i) (alice i) (honestAnswer (clauseAt formula i) bob) := by
  by_cases hs : localSatisfies (clauseAt formula i) (alice i) = true
  · by_cases h₁ : (alice i).first = bob (clauseAt formula i)[0].variableIndex <;>
      by_cases h₂ : (alice i).second = bob (clauseAt formula i)[1].variableIndex <;>
      by_cases h₃ : (alice i).third = bob (clauseAt formula i)[2].variableIndex <;>
      simp [eventsAt, accepts, acceptedSlots, matchingSlots, honestAnswer,
        answerAt, nameAt, hs, h₁, h₂, h₃]
  · simp [eventsAt, accepts, acceptedSlots, hs]

theorem accepted_enumerateEvents (formula : Formula) (alice : AliceStrategy formula)
    (bob : BobStrategy formula) (indices : List (Fin formula.clauses.length)) :
    ((enumerateEvents formula indices).filter (accepts formula alice bob)).length =
      acceptedCount formula alice bob indices := by
  induction indices with
  | nil => simp [enumerateEvents, acceptedCount]
  | cons i rest ih =>
    simp only [enumerateEvents, List.filter_append, List.length_append,
      accepted_eventsAt, ih, acceptedCount]

def allEvents (formula : Formula) : List (RandomEvent formula) :=
  enumerateEvents formula (allIndices formula)

theorem length_allEvents (formula : Formula) :
    (allEvents formula).length = 3 * formula.clauses.length := by
  simp [allEvents, length_enumerateEvents, allIndices]

theorem allEvents_nonempty (formula : Formula) (hne : formula.clauses ≠ []) :
    allEvents formula ≠ [] := by
  intro he
  have hl := length_allEvents formula
  rw [he] at hl
  have hpos : 0 < formula.clauses.length := List.length_pos_iff.mpr hne
  simp only [List.length_nil] at hl
  omega

theorem verifier_event_soundness (formula : Formula) (a b : Nat)
    (sourceGap : ∀ bob : BobStrategy formula,
      a * formula.clauses.length ≤ b * failureCount formula bob (allIndices formula))
    (alice : AliceStrategy formula) (bob : BobStrategy formula) :
    b * ((allEvents formula).filter (accepts formula alice bob)).length +
      a * formula.clauses.length ≤ b * (allEvents formula).length := by
  rw [length_allEvents]
  simp only [allEvents, accepted_enumerateEvents]
  exact hastad_basic_verifier_soundness formula a b sourceGap alice bob

def occurrencesAt {n : Nat} (clause : Clause n) (v : Fin n) : Nat :=
  (if clause[0].variableIndex = v then 1 else 0) +
  (if clause[1].variableIndex = v then 1 else 0) +
  (if clause[2].variableIndex = v then 1 else 0)

def occurrenceCount (formula : Formula) (v : Fin formula.«variables») :
    List (Fin formula.clauses.length) → Nat
  | [] => 0
  | i :: rest => occurrencesAt (clauseAt formula i) v + occurrenceCount formula v rest

theorem variable_eventsAt (formula : Formula) (v : Fin formula.«variables»)
    (i : Fin formula.clauses.length) :
    ((eventsAt formula i).filter (fun event =>
      decide (nameAt (clauseAt formula event.1) event.2 = v))).length =
      occurrencesAt (clauseAt formula i) v := by
  by_cases h₁ : (clauseAt formula i)[0].variableIndex = v <;>
    by_cases h₂ : (clauseAt formula i)[1].variableIndex = v <;>
    by_cases h₃ : (clauseAt formula i)[2].variableIndex = v <;>
    simp [eventsAt, nameAt, occurrencesAt, h₁, h₂, h₃]

theorem variable_enumerateEvents (formula : Formula) (v : Fin formula.«variables»)
    (indices : List (Fin formula.clauses.length)) :
    ((enumerateEvents formula indices).filter (fun event =>
      decide (nameAt (clauseAt formula event.1) event.2 = v))).length =
      occurrenceCount formula v indices := by
  induction indices with
  | nil => simp [enumerateEvents, occurrenceCount]
  | cons i rest ih =>
    simp only [enumerateEvents, List.filter_append, List.length_append,
      variable_eventsAt, ih, occurrenceCount]

theorem regular_bob_marginal (formula : Formula) (degree : Nat)
    (regular : ∀ v : Fin formula.«variables»,
      occurrenceCount formula v (allIndices formula) = degree)
    (v : Fin formula.«variables») :
    ((allEvents formula).filter (fun event =>
      decide (nameAt (clauseAt formula event.1) event.2 = v))).length = degree := by
  rw [allEvents, variable_enumerateEvents]
  exact regular v

end DFVSGames.Foundations.PCP

end OAI
