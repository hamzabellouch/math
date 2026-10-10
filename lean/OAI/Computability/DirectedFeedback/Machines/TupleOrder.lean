import Mathlib
import OAI.Computability.DirectedFeedback.Games.TestEmit

namespace OAI

namespace DFVSGames.Foundations.Complexity.MachineTupleOdometer
open Turing
open Reduction.MachineTransfer
variable {K Λ σ : Type} [DecidableEq K]
section Order
omit [DecidableEq K]
open scoped BigOperators

def tupleOrder (n q : ℕ) : List (Fin q → Fin n) :=
  List.ofFn (finFunctionFinEquiv (m := n) (n := q)).symm

theorem tupleOrder_length (n q : ℕ) : (tupleOrder n q).length = n ^ q := by
  simp [tupleOrder]

theorem tupleOrder_dimension_zero (n : ℕ) :
    tupleOrder n 0 = [fun i => Fin.elim0 i] := by
  simp only [tupleOrder, pow_zero, List.ofFn_succ, List.ofFn_zero, List.cons.injEq,
    and_true]
  funext i
  exact Fin.elim0 i

theorem tupleOrder_radix_zero {q : ℕ} (hq : 0 < q) : tupleOrder 0 q = [] := by
  apply List.length_eq_zero_iff.mp
  rw [tupleOrder_length, Nat.zero_pow hq]

theorem tupleRank_cons {n q : ℕ} (d : Fin n) (tail : Fin q → Fin n) :
    (finFunctionFinEquiv (Fin.cons d tail)).val =
      d.val + n * (finFunctionFinEquiv tail).val := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
  congr 1
  rw [finFunctionFinEquiv_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [pow_succ, Nat.mul_comm, Nat.mul_left_comm]

theorem tupleRank_increment_lowest {n q : ℕ} (d d' : Fin n)
    (tail : Fin q → Fin n) (hsucc : d'.val = d.val + 1) :
    (finFunctionFinEquiv (Fin.cons d' tail)).val =
      (finFunctionFinEquiv (Fin.cons d tail)).val + 1 := by
  rw [tupleRank_cons, tupleRank_cons, hsucc]
  omega

theorem tupleRank_carry {n q : ℕ} (hn : 0 < n) (d : Fin n)
    (tail tail' : Fin q → Fin n) (hmax : d.val = n - 1)
    (htail : (finFunctionFinEquiv tail').val = (finFunctionFinEquiv tail).val + 1) :
    (finFunctionFinEquiv (Fin.cons (⟨0, hn⟩ : Fin n) tail')).val =
      (finFunctionFinEquiv (Fin.cons d tail)).val + 1 := by
  rw [tupleRank_cons, tupleRank_cons, htail, hmax]
  simp only [Nat.zero_add, Nat.mul_add, Nat.mul_one]
  omega

theorem tupleRank_snoc {n q : ℕ} (tail : Fin q → Fin n) (d : Fin n) :
    (finFunctionFinEquiv (Fin.snoc tail d)).val =
      (finFunctionFinEquiv tail).val + d.val * n ^ q := by
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rfl

theorem tupleOrder_snoc (n q : ℕ) :
    tupleOrder n (q + 1) = (List.ofFn (fun d : Fin n => d)).flatMap
      (fun d => (tupleOrder n q).map (fun tail => Fin.snoc tail d)) := by
  rw [tupleOrder, List.ofFn_congr (Nat.pow_succ n q), List.ofFn_mul']
  simp only [tupleOrder, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext d
  apply congrArg List.ofFn
  funext rank
  dsimp only [Function.comp_apply]
  apply finFunctionFinEquiv.injective
  apply Fin.ext
  rw [Equiv.apply_symm_apply, tupleRank_snoc, Equiv.apply_symm_apply]
  simp [Nat.mul_comm, Nat.add_comm]

end Order

section Nested

open scoped BigOperators

structure CycleSchedule (K σ : Type) where
  currentSuffix : List Bool
  remainingSuffix : List Bool
  ambient : ℕ → σ
  register : ℕ → Option Bool
  base : ℕ → K → List Bool

abbrev Configuration (K Λ σ : Type) :=
  TM2.Cfg (Alphabet (K := K)) Λ (σ × Option Bool)

inductive NestedCycle (n : ℕ) (current remaining : ℕ → K) (bodyLabel : Λ)
    (checkLabel resetLabel : ℕ → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) :
    ℕ → Λ → Configuration K Λ σ → Configuration K Λ σ → Type where
  | leaf (exitLabel : Λ) (start finish : Configuration K Λ σ) (count : ℕ)
      (atBody : start.l = some bodyLabel) (atExit : finish.l = some exitLabel)
      (run : (MachineComposition.advance (TM2.step program))^[count] (some start) = some finish) :
      NestedCycle n current remaining bodyLabel checkLabel resetLabel program
        0 exitLabel start finish
  | node (depth : ℕ) (exitLabel : Λ) (positive : 0 < n)
      (distinct : current depth ≠ remaining depth)
      (atCheck : program (checkLabel depth) =
        increment (current depth) (remaining depth) bodyLabel (resetLabel depth))
      (atReset : program (resetLabel depth) =
        reset (current depth) (remaining depth) (resetLabel depth) exitLabel)
      (s : CycleSchedule K σ)
      (children : ∀ r : Fin n,
        NestedCycle n current remaining bodyLabel checkLabel resetLabel program
          depth (checkLabel depth)
          (bodyConfiguration (current depth) (remaining depth) bodyLabel (n - 1) r.val
            s.currentSuffix s.remainingSuffix s.ambient s.base)
          (checkConfiguration (current depth) (remaining depth) (checkLabel depth) (n - 1) r.val
            s.currentSuffix s.remainingSuffix s.ambient s.register s.base)) :
      NestedCycle n current remaining bodyLabel checkLabel resetLabel program
        (depth + 1) exitLabel
        (bodyConfiguration (current depth) (remaining depth) bodyLabel (n - 1) (n - 1)
          s.currentSuffix s.remainingSuffix s.ambient s.base)
        (cycleExit (current depth) (remaining depth) exitLabel (n - 1)
          s.currentSuffix s.remainingSuffix s.ambient s.base)

omit [DecidableEq K] in

def counterOverhead (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => n * (counterOverhead n q + 2)

namespace NestedCycle

variable {n : ℕ} {current remaining : ℕ → K} {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}
  {program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)}

def steps {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : ℕ :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count
  | .node _ _ _ _ _ _ _ children =>
    cycleSteps (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0) (n - 1) (n - 1)
termination_by depth

def LeafBound (B : ℕ) {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : Prop :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count ≤ B
  | .node _ _ _ _ _ _ _ children => ∀ r, LeafBound B (children r)
termination_by depth

def work {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : ℕ :=
  match tree with
  | .leaf _ _ _ count _ _ _ => count
  | .node _ _ _ _ _ _ _ children => ∑ r : Fin n, work (children r)
termination_by depth

def reverseDigit (d : Fin n) : Fin n := ⟨n - 1 - d.val, by omega⟩

theorem reverseDigit_current (d : Fin n) : n - 1 - (reverseDigit d).val = d.val := by
  dsimp only [reverseDigit]
  omega

def order {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : List (Fin depth → Fin n) :=
  match tree with
  | .leaf _ _ _ _ _ _ _ => [fun i => Fin.elim0 i]
  | .node _ _ _ _ _ _ _ children =>
    (List.ofFn (fun d : Fin n => d)).flatMap (fun d =>
      (order (children (reverseDigit d))).map (fun tail => Fin.snoc tail d))
termination_by depth

theorem order_eq_tupleOrder {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : tree.order = tupleOrder n depth := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run =>
    simpa only [order] using (tupleOrder_dimension_zero n).symm
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [order, ih, tupleOrder_snoc]

theorem order_length {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : tree.order.length = n ^ depth := by
  rw [order_eq_tupleOrder, tupleOrder_length]

theorem steps_eq_work_add_overhead {depth : ℕ} {exitLabel : Λ}
    {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) : tree.steps = tree.work + counterOverhead n depth := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run =>
    simp only [steps, work, counterOverhead, Nat.add_zero]
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    have hn : n - 1 + 1 = n := by omega
    have hsum : (∑ r ∈ Finset.range n,
        if hr : r < n then steps (children ⟨r, hr⟩) else 0) =
        (∑ r : Fin n, work (children r)) + n * counterOverhead n depth := by
      calc
        _ = ∑ r : Fin n, steps (children r) := by
          rw [← Fin.sum_univ_eq_sum_range]
          simp only [Fin.isLt, ↓reduceDIte]
        _ = ∑ r : Fin n, (work (children r) + counterOverhead n depth) := by
          apply Finset.sum_congr rfl
          intro r _
          exact ih r
        _ = _ := by simp [Finset.sum_add_distrib]
    simp only [steps, work, cycleSteps, hn, hsum, counterOverhead, Nat.mul_add]
    omega

theorem trace {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) :
    (MachineComposition.advance (TM2.step program))^[tree.steps] (some start) = some finish := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run => simpa only [steps] using run
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [steps]
    apply cycleTrace (current depth) (remaining depth) distinct bodyLabel (checkLabel depth)
      (resetLabel depth) exitLabel program atCheck atReset (n - 1) (n - 1)
      (Nat.le_refl _) s.currentSuffix s.remainingSuffix s.ambient s.register s.base
      (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0)
    intro r hr
    have hlt : r < n := by omega
    simpa only [dite_eq_left hlt] using ih ⟨r, hlt⟩

theorem steps_le {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (B : ℕ) (bounded : tree.LeafBound B) :
    tree.steps ≤ n ^ depth * B + counterOverhead n depth := by
  induction tree with
  | leaf exitLabel start finish count atBody atExit run =>
    simpa only [steps, LeafBound, counterOverhead, pow_zero, Nat.one_mul, Nat.add_zero] using bounded
  | node depth exitLabel positive distinct atCheck atReset s children ih =>
    simp only [LeafBound] at bounded
    have visits : VisitTraces (current depth) (remaining depth) bodyLabel (checkLabel depth)
        program (n - 1) (n - 1) s.currentSuffix s.remainingSuffix s.ambient s.register s.base
        (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0) := by
      intro r hr
      have hlt : r < n := by omega
      simpa only [dite_eq_left hlt] using (children ⟨r, hlt⟩).trace
    have bodyBound : ∀ r, r < n →
        (if hr : r < n then steps (children ⟨r, hr⟩) else 0) ≤
          n ^ depth * B + counterOverhead n depth := by
      intro r hr
      simpa only [dite_eq_left hr] using ih ⟨r, hr⟩ (bounded ⟨r, hr⟩)
    have h := (ascendingCycleInTime (current depth) (remaining depth) distinct bodyLabel
      (checkLabel depth) (resetLabel depth) exitLabel program atCheck atReset n positive
      s.currentSuffix s.remainingSuffix s.ambient s.register s.base
      (fun r => if hr : r < n then steps (children ⟨r, hr⟩) else 0)
      (n ^ depth * B + counterOverhead n depth) visits bodyBound).steps_le_m
    change cycleSteps _ (n - 1) (n - 1) ≤ _ at h
    simpa only [steps, counterOverhead, pow_succ, Nat.mul_add, Nat.add_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc] using h

def inTime {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (B : ℕ) (bounded : tree.LeafBound B) :
    StateTransition.EvalsToInTime (TM2.step program) start (some finish)
      (n ^ depth * B + counterOverhead n depth) where
  steps := tree.steps
  evals_in_steps := tree.trace
  steps_le_m := tree.steps_le B bounded

end NestedCycle

omit [DecidableEq K] in
theorem counterOverhead_le (n q : ℕ) (hn : 0 < n) :
    counterOverhead n q ≤ 2 * q * n ^ q := by
  induction q with
  | zero => simp [counterOverhead]
  | succ q ih =>
    have hp : 1 ≤ n ^ q := by apply Nat.one_le_pow; exact hn
    have h := Nat.mul_le_mul_left n (Nat.add_le_add_right ih 2)
    have htwo : 2 ≤ 2 * n ^ q := Nat.mul_le_mul_left 2 hp
    have hinner : 2 * q * n ^ q + 2 ≤ 2 * (q + 1) * n ^ q := by
      rw [Nat.mul_add, Nat.add_mul]
      omega
    exact h.trans (by
      simpa only [counterOverhead, pow_succ, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using Nat.mul_le_mul_left n hinner)

namespace NestedCycle

variable {n : ℕ} {current remaining : ℕ → K} {bodyLabel : Λ}
  {checkLabel resetLabel : ℕ → Λ}
  {program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)}

theorem steps_le_power {depth : ℕ} {exitLabel : Λ} {start finish : Configuration K Λ σ}
    (tree : NestedCycle n current remaining bodyLabel checkLabel resetLabel program
      depth exitLabel start finish) (hn : 0 < n) (B : ℕ) (bounded : tree.LeafBound B) :
    tree.steps ≤ (B + 2 * depth) * n ^ depth := by
  have h := (tree.steps_le B bounded).trans
    (Nat.add_le_add_left (counterOverhead_le n depth hn) (n ^ depth * B))
  simpa only [Nat.add_mul, Nat.mul_add, Nat.mul_comm] using h

end NestedCycle

end Nested


def entry (q : ℕ) (radix : K) (bodyLabel exitLabel : Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  if q = 0 then
    .load (fun state => (state.1, none)) (.goto fun _ => bodyLabel)
  else
    .peek radix (fun state head => (state.1, head))
      (.branch (fun state => state.2.getD false)
        (.load (fun state => (state.1, none)) (.goto fun _ => bodyLabel))
        (.load (fun state => (state.1, none)) (.goto fun _ => exitLabel)))

theorem entryStep_dimension_zero (radix : K) (startLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = entry 0 radix bodyLabel exitLabel)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some startLabel, (ambient, register), base⟩ =
      some ⟨some bodyLabel, (ambient, none), base⟩ := by
  change some (TM2.stepAux (program startLabel) (ambient, register) base) = _
  rw [atStart]
  simp [entry, TM2.stepAux]

theorem entryStep_radix_zero (q : ℕ) (hq : 0 < q) (radix : K)
    (startLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = entry q radix bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool) (hradix : base radix = encodeWord 0 ++ suffix)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some startLabel, (ambient, register), base⟩ =
      some ⟨some exitLabel, (ambient, none), base⟩ := by
  change some (TM2.stepAux (program startLabel) (ambient, register) base) = _
  rw [atStart]
  simp [entry, Nat.ne_of_gt hq, TM2.stepAux, hradix, encodeWord]

theorem entryStep_radix_positive (q n : ℕ) (hn : 0 < n) (radix : K)
    (startLabel bodyLabel exitLabel : Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStart : program startLabel = entry q radix bodyLabel exitLabel)
    (base : K → List Bool) (suffix : List Bool) (hradix : base radix = encodeWord n ++ suffix)
    (ambient : σ) (register : Option Bool) :
    TM2.step program ⟨some startLabel, (ambient, register), base⟩ =
      some ⟨some bodyLabel, (ambient, none), base⟩ := by
  cases n with
  | zero => omega
  | succ n =>
    change some (TM2.stepAux (program startLabel) (ambient, register) base) = _
    rw [atStart]
    by_cases hq : q = 0 <;>
      simp [entry, hq, TM2.stepAux, hradix, encodeWord, List.replicate_succ]

namespace Control

abbrev Label (q : ℕ) := Fin q ⊕ (Fin q ⊕ Option Bool)

def start (q : ℕ) : Label q := .inr (.inr none)
def body (q : ℕ) : Label q := .inr (.inr (some false))
def exit (q : ℕ) : Label q := .inr (.inr (some true))
def check {q : ℕ} (i : Fin q) : Label q := .inl i
def resetLabel {q : ℕ} (i : Fin q) : Label q := .inr (.inl i)

def carry {q : ℕ} (i : Fin q) : Label q :=
  if h : i.val + 1 < q then check ⟨i.val + 1, h⟩ else exit q

def program (q : ℕ) (current remaining : Fin q → K) (radix : K)
    (emitter : TM2.Stmt (Alphabet (K := K)) (Label q) (σ × Option Bool)) :
    Label q → TM2.Stmt (Alphabet (K := K)) (Label q) (σ × Option Bool)
  | .inl i => increment (current i) (remaining i) (body q) (resetLabel i)
  | .inr (.inl i) => reset (current i) (remaining i) (resetLabel i) (carry i)
  | .inr (.inr none) => entry q radix (body q) (exit q)
  | .inr (.inr (some false)) => emitter
  | .inr (.inr (some true)) => .halt

omit [DecidableEq K] in
theorem label_card (q : ℕ) : Fintype.card (Label q) = 2 * q + 3 := by
  simp [Label]
  omega

end Control


end DFVSGames.Foundations.Complexity.MachineTupleOdometer


section

namespace DFVSGames.Foundations.Hastad.SourceOccurrences.Encoding

open DFVSGames.Foundations.Complexity.MachineTupleOdometer

def decodeTuple {α β : Type} (a : Encoding α) (b : Encoding β)
    (digits : Fin a.size → Fin b.size) : α → β :=
  fun x => b.code.symm (digits (a.code x))

theorem enumerate_function {α β : Type} (a : Encoding α) (b : Encoding β) :
    (a.function b).enumerate =
      (tupleOrder b.size a.size).map (decodeTuple a b) := by
  simp only [tupleOrder, List.map_ofFn]
  rfl

theorem enumerate_fin_function (n u : ℕ) :
    ((Encoding.fin u).function (Encoding.fin n)).enumerate = tupleOrder n u := by
  rfl

end DFVSGames.Foundations.Hastad.SourceOccurrences.Encoding

namespace DFVSGames.Foundations.Hastad.SourceLoopOrder

open Complexity Complexity.MachineTupleOdometer
open Target SourceContexts SourceOccurrences
open DFVSGames.Reduction

def tupleTapeOrder (u D : ℕ) : List (SourceTape.TestTape (I u) (J u) D) :=
  (tupleOrder 2 (2 ^ u)).flatMap (fun f =>
    (tupleOrder D (8 ^ u)).flatMap (fun z =>
      (tupleOrder 2 (8 ^ u)).map (fun g =>
        (Encoding.decodeTuple (iEncoding u) Encoding.bool f,
         Encoding.decodeTuple (jEncoding u) (Encoding.fin D) z,
         Encoding.decodeTuple (jEncoding u) Encoding.bool g))))

theorem testTapeEncoding_eq_tupleTapeOrder (u D : ℕ) :
    (testTapeEncoding u D).enumerate = tupleTapeOrder u D := by
  rw [SourceEnumeration.testTapeEncoding_enumerate]
  simp only [tupleTapeOrder, Encoding.enumerate_function,
    List.flatMap_map, List.map_map, Function.comp_def]
  rfl

theorem testTapeEncoding_flatMap_tupleTapeOrder {α : Type} (u D : ℕ)
    (emit : SourceTape.TestTape (I u) (J u) D → List α) :
    (testTapeEncoding u D).enumerate.flatMap emit =
      (tupleTapeOrder u D).flatMap emit := by
  rw [testTapeEncoding_eq_tupleTapeOrder]

def rankedQuery (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (i : ℕ) : SourceQueryLoop.Query u D :=
  if h : i < (testTapeEncoding u D).size then
    (testTapeEncoding u D).code.symm ⟨i, h⟩
  else fallback

theorem rankedQuery_at (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (i : Fin (testTapeEncoding u D).size) :
    rankedQuery u D fallback i.val = (testTapeEncoding u D).code.symm i := by
  simp only [rankedQuery, i.isLt, ↓reduceDIte]

theorem query_prefixBits_eq_ofFn (u D n : ℕ) (queries : ℕ → SourceQueryLoop.Query u D)
    (values : Fin 3 → ℕ) (signature : SourceLocalSignature.Signature u) :
    SourceQueryLoop.prefixBits u D queries values signature n =
      (List.ofFn (fun i : Fin n => queries i.val)).flatMap
        (fun query => SourceTestAppend.equationBits u D values (signature, query)) := by
  induction n with
  | zero => simp [SourceQueryLoop.prefixBits]
  | succ n ih =>
    rw [SourceQueryLoop.prefixBits, List.ofFn_succ', List.concat_eq_append,
      List.flatMap_append]
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Fin.val_castSucc, Fin.val_last] using
      congrArg (fun bits => bits ++
        SourceTestAppend.equationBits u D values (signature, queries n)) ih

theorem query_prefixBits_eq_enumerate (u D : ℕ) (fallback : SourceQueryLoop.Query u D)
    (values : Fin 3 → ℕ) (signature : SourceLocalSignature.Signature u) :
    SourceQueryLoop.prefixBits u D (rankedQuery u D fallback) values signature
        (testTapeEncoding u D).size =
      (testTapeEncoding u D).enumerate.flatMap
        (fun query => SourceTestAppend.equationBits u D values (signature, query)) := by
  rw [query_prefixBits_eq_ofFn]
  have hlist : List.ofFn (fun i : Fin (testTapeEncoding u D).size =>
      rankedQuery u D fallback i.val) = (testTapeEncoding u D).enumerate := by
    apply congrArg List.ofFn
    funext i
    exact rankedQuery_at u D fallback i
  rw [hlist]

theorem query_prefixBits_eq_tupleTapeOrder (u D : ℕ)
    (fallback : SourceQueryLoop.Query u D) (values : Fin 3 → ℕ)
    (signature : SourceLocalSignature.Signature u) :
    SourceQueryLoop.prefixBits u D (rankedQuery u D fallback) values signature
        (testTapeEncoding u D).size =
      (tupleTapeOrder u D).flatMap
        (fun query => SourceTestAppend.equationBits u D values (signature, query)) := by
  rw [query_prefixBits_eq_enumerate, testTapeEncoding_eq_tupleTapeOrder]

def tupleSourceOrder (F : Formula) (u D : ℕ) : List (SourceIndex F u D) :=
  (tupleOrder F.clauses.length u).flatMap (fun c =>
    (tupleOrder 3 u).flatMap (fun s =>
      (tupleTapeOrder u D).map (fun t =>
        ((c, Encoding.decodeTuple (Encoding.fin u) slotEncoding s), t))))

theorem sourceIndexEncoding_eq_tupleSourceOrder (F : Formula) (u D : ℕ) :
    (sourceIndexEncoding F u D).enumerate = tupleSourceOrder F u D := by
  simp only [sourceIndexEncoding, Encoding.enumerate_prod,
    testTapeEncoding_eq_tupleTapeOrder, clauseEncoding, slotContextEncoding,
    Encoding.enumerate_function,
    List.flatMap_assoc, List.flatMap_map, tupleSourceOrder]
  rfl

theorem rawSourceList_eq_tupleOrder (F : Formula) (u D : ℕ) :
    rawSourceList F u D = (tupleSourceOrder F u D).map (sourceEquation F u D) := by
  unfold rawSourceList occurrenceList
  rw [sourceIndexEncoding_eq_tupleSourceOrder]

theorem sourceList_eq_tupleOrder (F : Formula) (u D : ℕ) (hne : F.clauses ≠ []) :
    sourceList F u D = (tupleSourceOrder F u D).map (sourceEquation F u D) := by
  rw [sourceList_nonempty F u D hne, rawSourceList_eq_tupleOrder]

theorem rawSourceList_flatMap_tupleOrder {α : Type} (F : Formula) (u D : ℕ)
    (emit : CloneGap.Equation (Fin (nBits F u)) → List α) :
    (rawSourceList F u D).flatMap emit =
      (tupleSourceOrder F u D).flatMap (fun p => emit (sourceEquation F u D p)) := by
  rw [rawSourceList_eq_tupleOrder]
  simp only [List.flatMap_map]

def reverseAppend {α β : Type} (encode : α → List β)
    (accumulator : List β) (record : α) : List β :=
  (encode record).reverse ++ accumulator

theorem foldl_reverseAppend {α β : Type} (encode : α → List β)
    (records : List α) (accumulator : List β) :
    records.foldl (reverseAppend encode) accumulator =
      (records.flatMap encode).reverse ++ accumulator := by
  induction records generalizing accumulator with
  | nil => simp
  | cons record records ih =>
    simp only [List.foldl_cons, ih, reverseAppend, List.flatMap_cons,
      List.reverse_append, List.append_assoc]

theorem foldl_reverseAppend_header {α β : Type} (encode : α → List β)
    (records : List α) (header : List β) :
    records.foldl (reverseAppend encode) header.reverse =
      (header ++ records.flatMap encode).reverse := by
  rw [foldl_reverseAppend, List.reverse_append]

theorem foldl_reverseAppend_prefix {α β : Type} (encode : α → List β)
    (emitted remaining : List α) (header : List β) :
    (emitted ++ remaining).foldl (reverseAppend encode) header.reverse =
      remaining.foldl (reverseAppend encode)
        (header ++ emitted.flatMap encode).reverse := by
  rw [List.foldl_append, foldl_reverseAppend_header]

theorem foldl_resultTapes {α K : Type} [DecidableEq K]
    (layout : SourceTestAppend.Layout K) (encode : α → List Bool)
    (records : List α) (base : K → List Bool) :
    records.foldl (fun tapes record =>
        SourceTestAppend.resultTapes layout tapes (encode record)) base =
      Function.update base layout.accumulator
        ((records.flatMap encode).reverse ++ base layout.accumulator) := by
  induction records generalizing base with
  | nil =>
    funext k
    by_cases hk : k = layout.accumulator <;> simp [hk]
  | cons record records ih =>
    simp only [List.foldl_cons, ih]
    funext k
    by_cases hk : k = layout.accumulator <;>
      simp [SourceTestAppend.resultTapes, hk, List.flatMap_cons,
        List.reverse_append, List.append_assoc]

theorem inputBits_eq_header_records (input : SourceEncoding.Input) :
    SourceEncoding.inputBits input =
      encodeWords [input.«variables», input.equations.length] ++
        input.equations.flatMap (fun e => encodeWords (SourceEncoding.equationWords e)) := by
  unfold SourceEncoding.inputBits SourceEncoding.inputWords
  rw [encodeWords_append]
  congr 1
  induction input.equations with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, encodeWords_append, ih]

theorem input_reverse_accumulator (input : SourceEncoding.Input) :
    input.equations.foldl
        (reverseAppend (fun e => encodeWords (SourceEncoding.equationWords e)))
        (encodeWords [input.«variables», input.equations.length]).reverse =
      (SourceEncoding.inputBits input).reverse := by
  rw [foldl_reverseAppend_header, inputBits_eq_header_records]

theorem sourceInput_tuple_reverse_accumulator (F : Formula) (u D : ℕ)
    (hD : 0 < D) (hne : F.clauses ≠ []) :
    (tupleSourceOrder F u D).foldl
        (reverseAppend (fun p => encodeWords
          (SourceEncoding.equationWords (sourceEquation F u D p))))
        (encodeWords [nBits F u, (sourceList F u D).length]).reverse =
      (SourceEncoding.inputBits (sourceInput F u D hD)).reverse := by
  rw [← input_reverse_accumulator (sourceInput F u D hD)]
  change _ = (sourceList F u D).foldl
    (reverseAppend (fun e => encodeWords (SourceEncoding.equationWords e)))
    (encodeWords [nBits F u, (sourceList F u D).length]).reverse
  rw [sourceList_eq_tupleOrder F u D hne, List.foldl_map]
  rfl

theorem finalReverse_steps (input : SourceEncoding.Input) (register : Option Bool) :
    MachineReverse.next^[(SourceEncoding.inputBits input).length + 1]
      (some (MachineReverse.running
        (input.equations.foldl
          (reverseAppend (fun e => encodeWords (SourceEncoding.equationWords e)))
          (encodeWords [input.«variables», input.equations.length]).reverse)
        [] register)) =
      some (MachineReverse.halted (SourceEncoding.inputBits input)) := by
  rw [input_reverse_accumulator]
  simpa only [List.length_reverse, List.reverse_reverse, List.append_nil] using
    MachineReverse.reverse_steps (SourceEncoding.inputBits input).reverse [] register

end DFVSGames.Foundations.Hastad.SourceLoopOrder

end


namespace DFVSGames.Foundations.Hastad.SourceOdometerSchedule

open Turing Complexity MachineTupleOdometer
open Reduction.MachineTransfer

abbrev Tape := SourceContextLoad.Tape

variable {u m : ℕ} {Extra Λ σ : Type} [DecidableEq Extra]

def currentAt (accumulator : Extra) (i : ℕ) : Tape u Extra :=
  if h : i < u then .current ⟨i, h⟩ else .extra accumulator

def remainingAt (accumulator : Extra) (i : ℕ) : Tape u Extra :=
  if h : i < u then .remaining ⟨i, h⟩ else .extra accumulator

def setDigits (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) : Tape u Extra → List Bool
  | .current i => if h : i.val < q then encodeWord (digits ⟨i.val, h⟩)
      else base (.current i)
  | .remaining i => if h : i.val < q then encodeWord (m - 1 - digits ⟨i.val, h⟩)
      else base (.remaining i)
  | k => base k

def setAcc (accumulator : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    Tape u Extra → List Bool := Function.update base (.extra accumulator) bits

def putDigit (i : Fin u) (base : Tape u Extra → List Bool) (d r : ℕ) :
    Tape u Extra → List Bool := digitTapes (.current i) (.remaining i) base d r [] []

omit [DecidableEq Extra] in
@[simp] theorem setDigits_zero (m : ℕ) (digits : Fin 0 → ℕ)
    (base : Tape u Extra → List Bool) : setDigits m digits base = base := by
  funext k
  cases k <;> simp [setDigits]

omit [DecidableEq Extra] in
@[simp] theorem setDigits_extra (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) (a : Extra) :
    setDigits m digits base (.extra a) = base (.extra a) := rfl

@[simp] theorem setAcc_self (a : Extra) (base : Tape u Extra → List Bool) :
    setAcc a base (base (.extra a)) = base := by
  simp [setAcc]

@[simp] theorem setAcc_setAcc (a : Extra) (base : Tape u Extra → List Bool)
    (first second : List Bool) : setAcc a (setAcc a base first) second = setAcc a base second := by
  simp [setAcc]

@[simp] theorem setAcc_apply (a : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    setAcc a base bits (.extra a) = bits := by simp [setAcc]

theorem setDigits_setAcc (m : ℕ) {q : ℕ} (digits : Fin q → ℕ)
    (a : Extra) (base : Tape u Extra → List Bool) (bits : List Bool) :
    setDigits m digits (setAcc a base bits) = setAcc a (setDigits m digits base) bits := by
  funext k
  cases k <;> simp [setDigits, setAcc, Function.update_apply]

@[simp] theorem putDigit_extra (i : Fin u) (base : Tape u Extra → List Bool)
    (d r : ℕ) (a : Extra) : putDigit i base d r (.extra a) = base (.extra a) := by
  simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

theorem putDigit_setAcc (i : Fin u) (base : Tape u Extra → List Bool)
    (d r : ℕ) (a : Extra) (bits : List Bool) :
    putDigit i (setAcc a base bits) d r = setAcc a (putDigit i base d r) bits := by
  funext k
  cases k <;> simp [putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
    setAcc, Function.update_apply]

theorem setDigits_putDigit (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (base : Tape u Extra → List Bool) (d r : ℕ) :
    setDigits m digits (putDigit ⟨q, hq⟩ base d r) =
      putDigit ⟨q, hq⟩ (setDigits m digits base) d r := by
  funext k
  cases k with
  | current i =>
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi, hne]
    · simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi,
        Function.update_apply]
  | remaining i =>
    by_cases hi : i.val < q
    · have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi, hne]
    · simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, hi,
        Function.update_apply]
  | _ => simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

theorem setDigits_snoc (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (d : ℕ) (base : Tape u Extra → List Bool) :
    setDigits m (Fin.snoc digits d) base =
      putDigit ⟨q, hq⟩ (setDigits m digits base) d (m - 1 - d) := by
  funext k
  cases k with
  | current i =>
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
        hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
          hi, hi', hne]
  | remaining i =>
    by_cases hi : i.val < q
    · have hi' : i.val < q + 1 := by omega
      have hne : i ≠ ⟨q, hq⟩ := by intro h; have := congrArg Fin.val h; simp at this; omega
      simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
        hi, hi', hne, Fin.snoc]
    · by_cases he : i.val = q
      · have hie : i = ⟨q, hq⟩ := Fin.ext he
        subst i
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt, Fin.snoc]
      · have hi' : ¬ i.val < q + 1 := by omega
        have hne : i ≠ ⟨q, hq⟩ := by intro h; exact he (congrArg Fin.val h)
        simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt,
          hi, hi', hne]
  | _ => simp [setDigits, putDigit, digitTapes, MachineUnaryAddAt.unaryTapes, tapesAt]

theorem setDigits_snoc_base (m q : ℕ) (hq : q < u) (digits : Fin q → ℕ)
    (d : ℕ) (base : Tape u Extra → List Bool) :
    setDigits m digits (putDigit ⟨q, hq⟩ base d (m - 1 - d)) =
      setDigits m (Fin.snoc digits d) base := by
  rw [setDigits_putDigit, setDigits_snoc]

def allBits {q : ℕ} (bits : (Fin q → Fin m) → List Bool) : List Bool :=
  (tupleOrder m q).flatMap bits

def blockPrefix (blocks : ℕ → List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => blockPrefix blocks n ++ blocks n

theorem blockPrefix_eq_ofFn (blocks : ℕ → List Bool) (n : ℕ) :
    blockPrefix blocks n = (List.ofFn (fun i : Fin n => blocks i.val)).flatten := by
  induction n with
  | zero => simp [blockPrefix]
  | succ n ih =>
    rw [blockPrefix, List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simpa only [Fin.val_castSucc, Fin.val_last, List.flatten_cons,
      List.flatten_nil, List.append_nil] using congrArg (fun xs => xs ++ blocks n) ih

def blocks {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) (d : ℕ) : List Bool :=
  if h : d < m then allBits (fun c => bits (Fin.snoc c ⟨d, h⟩)) else []

theorem blockPrefix_all {q : ℕ} (bits : (Fin (q + 1) → Fin m) → List Bool) :
    blockPrefix (blocks bits) m = allBits bits := by
  rw [blockPrefix_eq_ofFn]
  simp only [blocks, Fin.isLt, ↓reduceDIte, allBits, tupleOrder_snoc]
  simp only [List.flatMap_assoc, List.flatMap_map]
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_def]

def configuration (label : Λ) (canonical : σ) (tapes : Tape u Extra → List Bool) :
    Configuration (Tape u Extra) Λ σ := ⟨some label, (canonical, none), tapes⟩

def BodyTrace (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel returnLabel : Λ) (canonical : σ) (accumulator : Extra)
    {q : ℕ} (base : Tape u Extra → List Bool)
    (bits : (Fin q → Fin m) → List Bool) (B : ℕ) : Prop :=
  ∀ c output, ∃ count, count ≤ B ∧ (MachineComposition.advance (TM2.step program))^[count]
    (some (configuration bodyLabel canonical
      (setDigits m (fun i => (c i).val) (setAcc accumulator base output)))) =
    some (configuration returnLabel canonical
      (setDigits m (fun i => (c i).val)
        (setAcc accumulator base ((bits c).reverse ++ output))))

theorem val_snoc {q : ℕ} (c : Fin q → Fin m) (d : Fin m) :
    (fun i : Fin (q + 1) => (Fin.snoc (α := fun _ => Fin m) c d i).val) =
      Fin.snoc (fun i => (c i).val) d.val := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem zeros_snoc (q : ℕ) :
    Fin.snoc (fun _ : Fin q => (0 : ℕ)) 0 = fun _ : Fin (q + 1) => 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

def initialConfiguration (q : ℕ) (bodyLabel : Λ) (canonical : σ)
    (base : Tape u Extra → List Bool) : Configuration (Tape u Extra) Λ σ :=
  configuration bodyLabel canonical (setDigits m (fun _ : Fin q => 0) base)

def finalConfiguration {q : ℕ} (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (base : Tape u Extra → List Bool) (bits : (Fin q → Fin m) → List Bool) :
    Configuration (Tape u Extra) Λ σ :=
  configuration exitLabel canonical (setDigits m (fun _ : Fin q => 0)
    (setAcc accumulator base ((allBits bits).reverse ++ base (.extra accumulator))))

theorem exists_schedule
    (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ) (accumulator : Extra)
    (positive : 0 < m) (B q : ℕ) (hq : q ≤ u)
    (base : Tape u Extra → List Bool) (bits : (Fin q → Fin m) → List Bool)
    (atCheck : ∀ i, i < q → program (next i) =
      increment (currentAt accumulator i) (remainingAt accumulator i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < q → program (resetLabel i) =
      reset (currentAt accumulator i) (remainingAt accumulator i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical accumulator base bits B) :
    ∃ tree : NestedCycle m (currentAt accumulator) (remainingAt accumulator) bodyLabel
        next resetLabel program q (next q)
        (initialConfiguration (m := m) q bodyLabel canonical base)
        (finalConfiguration (next q) canonical accumulator base bits), tree.LeafBound B := by
  classical
  induction q generalizing base with
  | zero =>
    let empty : Fin 0 → Fin m := fun i => Fin.elim0 i
    obtain ⟨count, hcount, run⟩ := bodies empty (base (.extra accumulator))
    have hrun : (MachineComposition.advance (TM2.step program))^[count]
        (some (initialConfiguration (m := m) 0 bodyLabel canonical base)) =
        some (finalConfiguration (next 0) canonical accumulator base bits) := by
      simpa only [initialConfiguration, finalConfiguration, allBits,
        tupleOrder_dimension_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        setDigits_zero, setAcc_self] using run
    let tree := NestedCycle.leaf (n := m) (current := currentAt accumulator)
      (remaining := remainingAt accumulator) (bodyLabel := bodyLabel)
      (checkLabel := next) (resetLabel := resetLabel) (program := program)
      (next 0) (initialConfiguration (m := m) 0 bodyLabel canonical base)
      (finalConfiguration (next 0) canonical accumulator base bits) count rfl rfl hrun
    refine ⟨tree, ?_⟩
    unfold NestedCycle.LeafBound
    exact hcount
  | succ q ih =>
    have hqu : q < u := by omega
    let s : CycleSchedule (Tape u Extra) σ := {
      currentSuffix := []
      remainingSuffix := []
      ambient := fun _ => canonical
      register := fun _ => none
      base := fun r => setDigits m (fun _ : Fin q => 0)
        (setAcc accumulator base
          ((blockPrefix (blocks bits) (m - r)).reverse ++ base (.extra accumulator))) }
    have childrenExist (r : Fin m) :
        ∃ tree : NestedCycle m (currentAt accumulator) (remainingAt accumulator) bodyLabel
            next resetLabel program q (next q)
            (bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
              bodyLabel (m - 1) r.val s.currentSuffix s.remainingSuffix s.ambient s.base)
            (checkConfiguration (currentAt accumulator q) (remainingAt accumulator q)
              (next q) (m - 1) r.val s.currentSuffix s.remainingSuffix
              s.ambient s.register s.base), tree.LeafBound B := by
      let d : Fin m := NestedCycle.reverseDigit r
      let childBits : (Fin q → Fin m) → List Bool := fun c => bits (Fin.snoc c d)
      let childBase := putDigit ⟨q, hqu⟩
        (setAcc accumulator base
          ((blockPrefix (blocks bits) (m - (r.val + 1))).reverse ++ base (.extra accumulator)))
        d.val (m - 1 - d.val)
      have hrem : m - 1 - d.val = r.val := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hbefore : m - (r.val + 1) = d.val := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hafter : m - r.val = d.val + 1 := by
        dsimp [d, NestedCycle.reverseDigit]
        omega
      have hprefix : blockPrefix (blocks bits) (m - r.val) =
          blockPrefix (blocks bits) (m - (r.val + 1)) ++ allBits childBits := by
        rw [hafter, hbefore, blockPrefix]
        simp only [blocks, d.isLt, ↓reduceDIte, childBits]
      have childBodies : BodyTrace program bodyLabel (next 0) canonical accumulator
          childBase childBits B := by
        intro c output
        obtain ⟨count, hcount, h⟩ := bodies (Fin.snoc c d) output
        refine ⟨count, hcount, ?_⟩
        simpa only [childBase, childBits, ← putDigit_setAcc,
          setAcc_setAcc, setDigits_snoc_base, ← val_snoc] using h
      have lower := ih (by omega) childBase childBits
        (fun i hi => atCheck i (by omega)) (fun i hi => atReset i (by omega))
        childBodies
      have hstart : initialConfiguration (m := m) q bodyLabel canonical childBase =
          bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
            bodyLabel (m - 1) r.val s.currentSuffix s.remainingSuffix s.ambient s.base := by
        simp only [initialConfiguration, configuration, bodyConfiguration, s, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, setDigits_putDigit, hrem]
        rfl
      have hfinish : finalConfiguration (next q) canonical accumulator childBase childBits =
          checkConfiguration (currentAt accumulator q) (remainingAt accumulator q)
            (next q) (m - 1) r.val s.currentSuffix s.remainingSuffix
            s.ambient s.register s.base := by
        simp only [finalConfiguration, configuration, checkConfiguration, s, childBase,
          currentAt, remainingAt, hqu, ↓reduceDIte, putDigit_extra, setAcc_apply,
          ← putDigit_setAcc, setAcc_setAcc, setDigits_putDigit, hrem, hprefix,
          List.reverse_append, List.append_assoc]
        rfl
      rw [hstart, hfinish] at lower
      exact lower
    let children := fun r : Fin m => Classical.choose (childrenExist r)
    let tree := NestedCycle.node q (next (q + 1)) positive
      (by simp [currentAt, remainingAt, hqu])
      (atCheck q (by omega)) (atReset q (by omega)) s children
    have hbounded : tree.LeafBound B := by
      simp only [tree, NestedCycle.LeafBound]
      intro r
      exact Classical.choose_spec (childrenExist r)
    have hstart : bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
        bodyLabel (m - 1) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base =
        initialConfiguration (m := m) (q + 1) bodyLabel canonical base := by
      have hm : m - 1 + 1 = m := by omega
      simp only [bodyConfiguration, initialConfiguration, configuration, s,
        currentAt, remainingAt, hqu, ↓reduceDIte, Nat.sub_self, hm,
        blockPrefix, List.reverse_nil, List.nil_append, setAcc_self]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have hfinish : cycleExit (currentAt accumulator q) (remainingAt accumulator q)
        (next (q + 1)) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base =
        finalConfiguration (next (q + 1)) canonical accumulator base bits := by
      simp only [cycleExit, finalConfiguration, configuration, s, currentAt, remainingAt,
        hqu, ↓reduceDIte, Nat.sub_zero, blockPrefix_all]
      rw [← zeros_snoc q, setDigits_snoc m q hqu]
      rfl
    have result := (show ∃ t : NestedCycle m (currentAt accumulator) (remainingAt accumulator)
        bodyLabel next resetLabel program (q + 1) (next (q + 1))
        (bodyConfiguration (currentAt accumulator q) (remainingAt accumulator q)
          bodyLabel (m - 1) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base)
        (cycleExit (currentAt accumulator q) (remainingAt accumulator q)
          (next (q + 1)) (m - 1) s.currentSuffix s.remainingSuffix s.ambient s.base),
        t.LeafBound B from ⟨tree, hbounded⟩)
    rw [hstart, hfinish] at result
    exact result

theorem traversalInTime
    (program : Λ → TM2.Stmt (fun _ : Tape u Extra => Bool) Λ (σ × Option Bool))
    (bodyLabel : Λ) (next resetLabel : ℕ → Λ) (canonical : σ) (accumulator : Extra)
    (positive : 0 < m) (B : ℕ) (base : Tape u Extra → List Bool)
    (bits : (Fin u → Fin m) → List Bool)
    (atCheck : ∀ i, i < u → program (next i) =
      increment (currentAt accumulator i) (remainingAt accumulator i) bodyLabel (resetLabel i))
    (atReset : ∀ i, i < u → program (resetLabel i) =
      reset (currentAt accumulator i) (remainingAt accumulator i) (resetLabel i) (next (i + 1)))
    (bodies : BodyTrace program bodyLabel (next 0) canonical accumulator base bits B) :
    Nonempty (StateTransition.EvalsToInTime (TM2.step program)
      (initialConfiguration (m := m) u bodyLabel canonical base)
      (some (finalConfiguration (next u) canonical accumulator base bits))
      ((B + 2 * u) * m ^ u)) := by
  obtain ⟨tree, ht⟩ := exists_schedule program bodyLabel next resetLabel canonical accumulator
    positive B u (Nat.le_refl _) base bits atCheck atReset bodies
  exact ⟨{
    steps := tree.steps
    evals_in_steps := tree.trace
    steps_le_m := tree.steps_le_power positive B ht }⟩

omit [DecidableEq Extra] in
@[simp] theorem initial_current (base : Tape u Extra → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin u) :
    (initialConfiguration (m := m) u bodyLabel canonical base).stk (.current i) =
      encodeWord 0 := by simp [initialConfiguration, configuration, setDigits]

omit [DecidableEq Extra] in
@[simp] theorem initial_remaining (base : Tape u Extra → List Bool)
    (bodyLabel : Λ) (canonical : σ) (i : Fin u) :
    (initialConfiguration (m := m) u bodyLabel canonical base).stk (.remaining i) =
      encodeWord (m - 1) := by simp [initialConfiguration, configuration, setDigits]

@[simp] theorem final_current (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) (i : Fin u) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.current i) =
      encodeWord 0 := by simp [finalConfiguration, configuration, setDigits]

@[simp] theorem final_remaining (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) (i : Fin u) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.remaining i) =
      encodeWord (m - 1) := by simp [finalConfiguration, configuration, setDigits]

@[simp] theorem final_accumulator (base : Tape u Extra → List Bool)
    (exitLabel : Λ) (canonical : σ) (accumulator : Extra)
    (bits : (Fin u → Fin m) → List Bool) :
    (finalConfiguration exitLabel canonical accumulator base bits).stk (.extra accumulator) =
      ((tupleOrder m u).flatMap bits).reverse ++ base (.extra accumulator) := by
  simp [finalConfiguration, configuration, allBits]

end DFVSGames.Foundations.Hastad.SourceOdometerSchedule

end OAI
