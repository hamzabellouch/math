import Mathlib
import OAI.Computability.MinUncut.PCP.ContextPrepare
import OAI.Computability.MinUncut.PCP.DescriptorEmission

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceRuntimeModel

open Turing Complexity SourceContexts SourceOccurrences SourceLocalSignature SourceProfileBridge

inductive BodyWork (Extra : Type)
  | leftBlock | dummy | bitCount | occurrenceCount
  | zero | rank | rightBase | leftBase
  | accA | accB | counter | arithScratch | coefficient
  | queryTemporary | queryScratch | accumulator
  | extra (value : Extra)
  deriving DecidableEq, Fintype

abbrev BodyExtra (Extra : Type) := SourceLoopInit.HeaderTape ⊕ BodyWork Extra
abbrev Arena (u : Nat) (Extra : Type) := SourceContextLoad.Tape u (BodyExtra Extra)
abbrev QueryState (u D : Nat) := SourceQueryLoop.State u D
abbrev ArithmeticState := MachineHorner.State Unit
abbrev State (u D : Nat) := SourceContextPrepare.State u (QueryState u D × ArithmeticState)
abbrev QueryMetadata (u : Nat) := SourceContextPrepare.LoadState ×
  (SourceSignaturePrepare.ProfileState u × (Signature u × ArithmeticState))
abbrev ArithmeticMetadata (u D : Nat) := SourceContextPrepare.LoadState ×
  (SourceSignaturePrepare.ProfileState u × (Signature u × QueryState u D))

variable {u D : Nat} {Extra : Type}

def workTape (role : BodyWork Extra) : Arena u Extra := .extra (.inr role)
def variableHeader : Arena u Extra := SourceLoopInit.variableHeader
def clauseHeader : Arena u Extra := SourceLoopInit.clauseHeader

def canonicalSignature (u : Nat) : Signature u :=
  ⟨fun _ => false, fun _ _ => false, fun _ => .first⟩

def canonicalState (initialQuery : SourceQueryLoop.Query u D) : State u D :=
  SourceContextPrepare.initialState (fun _ _ => false) (canonicalSignature u)
    (((canonicalSignature u, initialQuery), none), (((), ()), none))

def queryStateEquiv (u D : Nat) : QueryState u D × QueryMetadata u ≃ State u D where
  toFun x := (x.2.1, (x.2.2.1, (x.2.2.2.1, (x.1, x.2.2.2.2))))
  invFun x := (x.2.2.2.1, (x.1, (x.2.1, (x.2.2.1, x.2.2.2.2))))
  left_inv _ := rfl
  right_inv _ := rfl

def arithmeticStateEquiv (u D : Nat) : ArithmeticState × ArithmeticMetadata u D ≃ State u D where
  toFun x := (x.2.1, (x.2.2.1, (x.2.2.2.1, (x.2.2.2.2, x.1))))
  invFun x := (x.2.2.2.2, (x.1, (x.2.1, (x.2.2.1, x.2.2.2.1))))
  left_inv _ := rfl
  right_inv _ := rfl

def rankControls (header : SourceLoopInit.HeaderTape) : Fin 6 ↪ BodyExtra Extra where
  toFun
    | 0 => .inl header
    | 1 => .inr .accA
    | 2 => .inr .accB
    | 3 => .inr .rank
    | 4 => .inr .counter
    | 5 => .inr .arithScratch
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def clauseRankSlots : MachineHorner.Layout u ↪ Arena u Extra :=
  SourceRankPhase.clauseSlots (rankControls .clauseCount)

def variableRankSlots (selected : SlotContext u) : MachineHorner.Layout u ↪ Arena u Extra :=
  SourceRankPhase.variableSlots (rankControls .variableCount) selected

def baseSlots (right : Bool) : MachineHorner.Layout 2 ↪ Arena u Extra where
  toFun
    | .inl 0 => workTape .rank
    | .inl 1 => workTape .accA
    | .inl 2 => workTape .accB
    | .inl 3 => workTape (if right then .rightBase else .leftBase)
    | .inl 4 => workTape .counter
    | .inl 5 => workTape .arithScratch
    | .inr 0 => workTape .coefficient
    | .inr 1 => workTape (if right then .leftBlock else .zero)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => cases right <;> fin_cases a <;> fin_cases b <;> simp_all [workTape]
      | inr b => cases right <;> fin_cases a <;> fin_cases b <;> simp_all [workTape]
    | inr a =>
      cases b with
      | inl b => cases right <;> fin_cases a <;> fin_cases b <;> simp_all [workTape]
      | inr b => cases right <;> fin_cases a <;> fin_cases b <;> simp_all [workTape]

def querySources : Fin 3 → Arena u Extra
  | 0 => workTape .leftBase
  | 1 => workTape .rightBase
  | 2 => workTape .dummy

def queryLayout : SourceTestAppend.Layout (Arena u Extra) where
  sources := querySources
  temporary := workTape .queryTemporary
  scratch := workTape .queryScratch
  accumulator := workTape .accumulator
  sourceTemporary side := by fin_cases side <;> simp [querySources, workTape]
  sourceScratch side := by fin_cases side <;> simp [querySources, workTape]
  sourceAccumulator side := by fin_cases side <;> simp [querySources, workTape]
  temporaryScratch := by simp [workTape]
  temporaryAccumulator := by simp [workTape]
  scratchAccumulator := by simp [workTape]

def perSlotCleanup : List (Arena u Extra) := [workTape .rank, workTape .leftBase]
def finalBaseCleanup : List (Arena u Extra) := [workTape .rank, workTape .rightBase, workTape .zero]

@[simp] theorem initializer_arena :
    SourceLoopInit.Tape u (BodyWork Extra) = Arena u Extra := rfl

end MinUncutGames.Foundations.Hastad.SourceRuntimeModel

end
section
namespace MinUncutGames.Foundations.Complexity.CookLevin.PolynomialMachine

noncomputable def coefficientPolynomial : List Nat → Polynomial Nat
  | [] => 0
  | a :: rest => coefficientPolynomial rest * Polynomial.X + Polynomial.C a

theorem coefficientPolynomial_eval (cs : List Nat) (n : Nat) :
    (coefficientPolynomial cs).eval n = cs.foldr (fun digit value => value * n + digit) 0 := by
  induction cs with
  | nil => simp [coefficientPolynomial]
  | cons a rest ih => simp [coefficientPolynomial, ih]

theorem coefficientPolynomial_eval_reverse (cs : List Nat) (n : Nat) :
    (coefficientPolynomial cs).eval n =
      cs.reverse.foldl (fun value digit => value * n + digit) 0 := by
  rw [coefficientPolynomial_eval, List.foldr_eq_foldl_reverse]

noncomputable def coefficients (p : Polynomial Nat) :
    {cs : List Nat // coefficientPolynomial cs = p} := by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact ⟨[], rfl⟩
  · intro q a hq ha ih
    rcases ih with ⟨cs, hcs⟩
    cases cs with
    | nil =>
      refine ⟨[a], ?_⟩
      rw [← hcs]
      simp [coefficientPolynomial]
    | cons b rest =>
      refine ⟨(b + a) :: rest, ?_⟩
      rw [← hcs]
      simp only [coefficientPolynomial, Polynomial.C_add, add_assoc]
  · intro q hq ih
    rcases ih with ⟨cs, hcs⟩
    refine ⟨0 :: cs, ?_⟩
    simp only [coefficientPolynomial, Polynomial.C_0, add_zero, hcs]

noncomputable def highCoefficients (p : Polynomial Nat) : List Nat :=
  (coefficients p).val.reverse

noncomputable def width (p : Polynomial Nat) : Nat := (highCoefficients p).length

noncomputable def digit (p : Polynomial Nat) (i : Nat) : Nat :=
  if hi : i < width p then (highCoefficients p)[i] else 0

noncomputable def digitBound (p : Polynomial Nat) : Nat := (highCoefficients p).sum

theorem le_sum_of_mem {n : Nat} {xs : List Nat} (h : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons a rest ih =>
    rcases List.mem_cons.mp h with rfl | hm
    · simp
    · have hrest := ih hm
      simp only [List.sum_cons]
      omega

theorem digit_le_bound (p : Polynomial Nat) (i : Nat) : digit p i ≤ digitBound p := by
  unfold digit
  split
  · exact le_sum_of_mem (List.getElem_mem _)
  · exact Nat.zero_le _

theorem highCoefficients_foldl (p : Polynomial Nat) (n : Nat) :
    (highCoefficients p).foldl (fun value digit => value * n + digit) 0 = p.eval n := by
  calc
    _ = (coefficientPolynomial (coefficients p).val).eval n :=
      (coefficientPolynomial_eval_reverse (coefficients p).val n).symm
    _ = p.eval n := congrArg (fun q : Polynomial Nat => q.eval n) (coefficients p).property

theorem range_map_digit (p : Polynomial Nat) :
    (List.range (width p)).map (digit p) = highCoefficients p := by
  apply List.ext_getElem
  · simp [width]
  · intro i hi hj
    simp [digit, width, hj]

section LiteralFields

open Turing
open MinUncutGames.Reduction.MachineSubstitution

variable {K Λ σ : Type} [DecidableEq K]

def prependFields (word : K → List Bool) : List K →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], continuation => continuation
  | k :: rest, continuation =>
      pushWord k (word k).reverse (prependFields word rest continuation)

def prependFieldsTapes (word : K → List Bool) : List K →
    (K → List Bool) → K → List Bool
  | [], tapes => tapes
  | k :: rest, tapes =>
      prependFieldsTapes word rest (Function.update tapes k (word k ++ tapes k))

theorem stepAux_prependFields (word : K → List Bool) (indices : List K)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (prependFields word indices continuation) state tapes =
      TM2.stepAux continuation state (prependFieldsTapes word indices tapes) := by
  induction indices generalizing tapes with
  | nil => rfl
  | cons k rest ih =>
    simp only [prependFields, stepAux_pushWord, List.reverse_reverse, prependFieldsTapes]
    exact ih _

theorem prependFieldsTapes_apply (word : K → List Bool) (indices : List K)
    (hn : indices.Nodup) (tapes : K → List Bool) (k : K) :
    prependFieldsTapes word indices tapes k =
      if k ∈ indices then word k ++ tapes k else tapes k := by
  induction indices generalizing tapes with
  | nil => simp [prependFieldsTapes]
  | cons j rest ih =>
    have hnodup := List.nodup_cons.mp hn
    rw [prependFieldsTapes, ih hnodup.2]
    by_cases hkj : k = j
    · subst k
      simp [hnodup.1]
    · simp [hkj]

def popN (k : K) : Nat → TM2.Stmt (fun _ : K => Bool) Λ σ →
    TM2.Stmt (fun _ : K => Bool) Λ σ
  | 0, continuation => continuation
  | n + 1, continuation => .pop k (fun state _ => state) (popN k n continuation)

theorem stepAux_popN (k : K) (n : Nat)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (popN k n continuation) state tapes =
      TM2.stepAux continuation state (Function.update tapes k ((tapes k).drop n)) := by
  induction n generalizing tapes with
  | zero => simp [popN]
  | succ n ih =>
    simp only [popN, TM2.stepAux]
    rw [ih]
    simp only [Function.update_self, Function.update_idem, List.drop_tail]

def clearFields (count : K → Nat) : List K →
    TM2.Stmt (fun _ : K => Bool) Λ σ → TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], continuation => continuation
  | k :: rest, continuation => popN k (count k) (clearFields count rest continuation)

def clearFieldsTapes (count : K → Nat) : List K → (K → List Bool) → K → List Bool
  | [], tapes => tapes
  | k :: rest, tapes => clearFieldsTapes count rest
      (Function.update tapes k ((tapes k).drop (count k)))

theorem stepAux_clearFields (count : K → Nat) (indices : List K)
    (continuation : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (clearFields count indices continuation) state tapes =
      TM2.stepAux continuation state (clearFieldsTapes count indices tapes) := by
  induction indices generalizing tapes with
  | nil => rfl
  | cons k rest ih =>
    simp only [clearFields, stepAux_popN, clearFieldsTapes]
    exact ih _

theorem clearFieldsTapes_apply (count : K → Nat) (indices : List K)
    (hn : indices.Nodup) (tapes : K → List Bool) (k : K) :
    clearFieldsTapes count indices tapes k =
      if k ∈ indices then (tapes k).drop (count k) else tapes k := by
  induction indices generalizing tapes with
  | nil => simp [clearFieldsTapes]
  | cons j rest ih =>
    have hnodup := List.nodup_cons.mp hn
    rw [clearFieldsTapes, ih hnodup.2]
    by_cases hkj : k = j
    · subst k
      simp [hnodup.1]
    · simp [hkj]

end LiteralFields

noncomputable section

abbrev Layout (p : Polynomial Nat) := MachineHorner.Layout (width p)
abbrev Label (p : Polynomial Nat) := Unit ⊕ (MachineHorner.Label (width p) ⊕ Bool)
abbrev State := MachineHorner.State Unit

def fieldWord (p : Polynomial Nat) : Layout p → List Bool
  | .inl _ => []
  | .inr i => encodeWord (digit p i.val)

def fieldIndices (p : Polynomial Nat) : List (Layout p) :=
  (List.finRange (width p)).map Sum.inr

theorem fieldIndices_nodup (p : Polynomial Nat) : (fieldIndices p).Nodup :=
  (List.nodup_finRange _).map Sum.inr_injective

@[simp] theorem inl_not_mem_fields (p : Polynomial Nat) (i : Fin 6) :
    Sum.inl i ∉ fieldIndices p := by simp [fieldIndices]

@[simp] theorem inr_mem_fields (p : Polynomial Nat) (i : Fin (width p)) :
    Sum.inr i ∈ fieldIndices p := by simp [fieldIndices]

def initialTapes (p : Polynomial Nat) (n : Nat) (k : Layout p) : List Bool :=
  if k = .inl 0 then encodeWord n else []

def preparedTapes (p : Polynomial Nat) (n : Nat) : Layout p → List Bool :=
  prependFieldsTapes (fieldWord p) (fieldIndices p) (initialTapes p n)

@[simp] theorem preparedTapes_inl (p : Polynomial Nat) (n : Nat) (i : Fin 6) :
    preparedTapes p n (.inl i) = if i = 0 then encodeWord n else [] := by
  rw [preparedTapes, prependFieldsTapes_apply _ _ (fieldIndices_nodup p)]
  simp [initialTapes]

@[simp] theorem preparedTapes_inr (p : Polynomial Nat) (n : Nat) (i : Fin (width p)) :
    preparedTapes p n (.inr i) = encodeWord (digit p i.val) := by
  rw [preparedTapes, prependFieldsTapes_apply _ _ (fieldIndices_nodup p)]
  simp [initialTapes, fieldWord]

def slots (p : Polynomial Nat) : Layout p ↪ Layout p := Function.Embedding.refl _

theorem preparedTapes_clean (p : Polynomial Nat) (n : Nat) :
    MachineHorner.Clean (slots p) (preparedTapes p n) := by
  constructor <;> simp [slots]

def innerLabels (p : Polynomial Nat) (l : MachineHorner.Label (width p)) : Label p :=
  .inr (.inl l)

def program (p : Polynomial Nat) : Label p →
    Turing.TM2.Stmt (fun _ : Layout p => Bool) (Label p) State
  | .inl _ => prependFields (fieldWord p) (fieldIndices p)
      (.goto fun _ => innerLabels p .start)
  | .inr (.inl l) => MachineHorner.statement (slots p) (innerLabels p)
      (some (.inr (.inr false))) l
  | .inr (.inr false) => MachineLookup.discard (.inl 0)
      (.inr (.inr false)) (.inr (.inr true))
  | .inr (.inr true) => clearFields (fun k => (fieldWord p k).length) (fieldIndices p) .halt

abbrev machine (p : Polynomial Nat) : Turing.FinTM2 where
  K := Layout p
  k₀ := .inl 0
  k₁ := .inl 3
  Γ _ := Bool
  Λ := Label p
  main := .inl ()
  σ := State
  initialState := (((), ()), none)
  m := program p

def afterHornerTapes (p : Polynomial Nat) (n result : Nat) : Layout p → List Bool :=
  Function.update (preparedTapes p n) (.inl 3) (encodeWord result)

def afterInputTapes (p : Polynomial Nat) (n result : Nat) : Layout p → List Bool :=
  Function.update (afterHornerTapes p n result) (.inl 0) []

def finalTapes (p : Polynomial Nat) (result : Nat) (k : Layout p) : List Bool :=
  if k = .inl 3 then encodeWord result else []

theorem clearFields_final (p : Polynomial Nat) (n result : Nat) :
    clearFieldsTapes (fun k => (fieldWord p k).length) (fieldIndices p)
      (afterInputTapes p n result) = finalTapes p result := by
  funext k
  rw [clearFieldsTapes_apply _ _ (fieldIndices_nodup p)]
  cases k with
  | inl i =>
    fin_cases i <;> simp [afterInputTapes, afterHornerTapes, finalTapes]
  | inr i =>
    simp [afterInputTapes, afterHornerTapes, fieldWord, finalTapes]

theorem initList_eq (p : Polynomial Nat) (n : Nat) :
    Turing.initList (machine p) (encodeWord n) =
      ⟨some (.inl ()), (((), ()), none), initialTapes p n⟩ := by
  unfold Turing.initList
  congr 1

theorem haltList_eq (p : Polynomial Nat) (result : Nat) :
    Turing.haltList (machine p) (encodeWord result) =
      ⟨none, (((), ()), none), finalTapes p result⟩ := by
  unfold Turing.haltList
  congr 1

theorem initializationTrace (p : Polynomial Nat) (n : Nat) :
    (MachineComposition.advance (machine p).step)^[1]
      (some (Turing.initList (machine p) (encodeWord n))) =
      some ⟨some (innerLabels p .start), (((), ()), none), preparedTapes p n⟩ := by
  rw [initList_eq]
  change some (Turing.TM2.stepAux (program p (.inl ()))
    (((), ()), none) (initialTapes p n)) = _
  rw [program, stepAux_prependFields]
  rfl

theorem cleanupTrace (p : Polynomial Nat) (n result : Nat) :
    (MachineComposition.advance (machine p).step)^[n + 2]
      (some ⟨some (.inr (.inr false)), (((), ()), none), afterHornerTapes p n result⟩) =
      some (Turing.haltList (machine p) (encodeWord result)) := by
  have hd := MachineLookup.discardTrace (Sum.inl (0 : Fin 6))
    (Sum.inr (Sum.inr false)) (Sum.inr (Sum.inr true)) (program p) rfl
    (afterHornerTapes p n result) n [] (by simp [afterHornerTapes]) ((), ()) none
  have hc : (MachineComposition.advance (machine p).step)^[1]
      (some ⟨some (.inr (.inr true)), (((), ()), none), afterInputTapes p n result⟩) =
      some (Turing.haltList (machine p) (encodeWord result)) := by
    change some (Turing.TM2.stepAux (program p (.inr (.inr true)))
      (((), ()), none) (afterInputTapes p n result)) = _
    rw [program, stepAux_clearFields, clearFields_final, haltList_eq]
    rfl
  rw [show n + 2 = 1 + (n + 1) by omega, Function.iterate_add_apply]
  exact (congrArg ((MachineComposition.advance (Turing.TM2.step (program p)))^[1]) hd).trans hc

def prefixValuePolynomial (digits : Nat → Nat) : Nat → Polynomial Nat
  | 0 => 0
  | i + 1 => Polynomial.X * prefixValuePolynomial digits i + Polynomial.C (digits i)

def prefixCostPolynomial (digits : Nat → Nat) : Nat → Polynomial Nat
  | 0 => 0
  | i + 1 => prefixCostPolynomial digits i +
      Polynomial.C 3 * Polynomial.X * prefixValuePolynomial digits i +
      Polynomial.C 9 * prefixValuePolynomial digits i + Polynomial.C (3 * digits i + 14)

theorem prefixValuePolynomial_eval (digits : Nat → Nat) (i n : Nat) :
    (prefixValuePolynomial digits i).eval n = MachineHorner.value n digits i := by
  induction i with
  | zero => simp [prefixValuePolynomial, MachineHorner.value]
  | succ i ih => simp [prefixValuePolynomial, MachineHorner.value, ih]

theorem prefixCostPolynomial_eval (digits : Nat → Nat) (i n : Nat) :
    (prefixCostPolynomial digits i).eval n = MachineHorner.prefixSteps n digits i := by
  induction i with
  | zero => simp [prefixCostPolynomial, MachineHorner.prefixSteps]
  | succ i ih =>
    simp only [prefixCostPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, prefixValuePolynomial_eval, ih,
      MachineHorner.prefixSteps, MachineHorner.stepCost, MachineRadixStep.steps]
    ring

def timePolynomial (p : Polynomial Nat) : Polynomial Nat :=
  prefixCostPolynomial (digit p) (width p) +
    Polynomial.C 2 * prefixValuePolynomial (digit p) (width p) + Polynomial.X + Polynomial.C 8

theorem timePolynomial_eval (p : Polynomial Nat) (n : Nat) :
    (timePolynomial p).eval n = MachineHorner.steps n (digit p) (width p) + n + 3 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, prefixValuePolynomial_eval,
    prefixCostPolynomial_eval, MachineHorner.steps]
  omega

theorem hornerValue_eq_eval (p : Polynomial Nat) (n : Nat) :
    MachineHorner.value n (digit p) (width p) = p.eval n := by
  rw [MachineHorner.value_eq_foldl, range_map_digit]
  have hh := highCoefficients_foldl p n
  simpa only [Nat.mul_comm] using hh

theorem hornerStageTrace (p : Polynomial Nat) (n : Nat) :
    (MachineComposition.advance (machine p).step)^[MachineHorner.steps n (digit p) (width p)]
      (some ⟨some (innerLabels p .start), (((), ()), none), preparedTapes p n⟩) =
      some ⟨some (.inr (.inr false)), (((), ()), none), afterHornerTapes p n (p.eval n)⟩ := by
  have h := MachineHorner.hornerTrace (slots p) (innerLabels p)
    (some (.inr (.inr false))) (program p) (fun _ => rfl) (preparedTapes p n) n (digit p)
    (by simp [slots]) (fun i => by simp [slots]) (preparedTapes_clean p n) () none
  rw [hornerValue_eq_eval] at h
  have ht : MachineHorner.resultTapes (slots p) (preparedTapes p n) (p.eval n) =
      afterHornerTapes p n (p.eval n) := by
    simp [MachineHorner.resultTapes, afterHornerTapes, slots]
  rw [ht] at h
  exact h

def outputsInTime (p : Polynomial Nat) (n : Nat) :
    Turing.TM2OutputsInTime (machine p) (encodeWord n) (some (encodeWord (p.eval n)))
      ((timePolynomial p).eval n) where
  steps := MachineHorner.steps n (digit p) (width p) + n + 3
  evals_in_steps := by
    change (MachineComposition.advance (machine p).step)^[MachineHorner.steps n (digit p) (width p) + n + 3]
      (some (Turing.initList (machine p) (encodeWord n))) =
        some (Turing.haltList (machine p) (encodeWord (p.eval n)))
    have h01 : (MachineComposition.advance (machine p).step)^[
        MachineHorner.steps n (digit p) (width p) + 1]
        (some (Turing.initList (machine p) (encodeWord n))) =
          some ⟨some (.inr (.inr false)), (((), ()), none),
            afterHornerTapes p n (p.eval n)⟩ := by
      rw [Function.iterate_add_apply, initializationTrace, hornerStageTrace]
    rw [show MachineHorner.steps n (digit p) (width p) + n + 3 =
      (n + 2) + (MachineHorner.steps n (digit p) (width p) + 1) by omega,
      Function.iterate_add_apply, h01, cleanupTrace]
  steps_le_m := by rw [timePolynomial_eval]

def computableInPolyTime (p : Polynomial Nat) :
    Turing.TM2ComputableInPolyTime encodeWord encodeWord p.eval where
  tm := machine p
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial p
  outputsFun n := by
    change Turing.TM2OutputsInTime (machine p) ((encodeWord n).map id)
      (some ((encodeWord (p.eval n)).map id)) ((timePolynomial p).eval (encodeWord n).length)
    rw [List.map_id, List.map_id, encodeWord_length]
    let h := outputsInTime p n
    exact {
      toEvalsTo := h.toEvalsTo
      steps_le_m := h.steps_le_m.trans
        (MachineComposition.natPolynomial_eval_mono (timePolynomial p) (by omega : n ≤ n + 1)) }

end

end MinUncutGames.Foundations.Complexity.CookLevin.PolynomialMachine

end

end OAI
