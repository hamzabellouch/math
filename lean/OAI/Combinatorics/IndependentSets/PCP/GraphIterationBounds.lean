import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.TableIteration
import OAI.Combinatorics.IndependentSets.Machines.GraphCounterPrefix

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.GraphIterationBounds

open PCP RoundTables

def inputBits (input : Input) : List Bool := GraphTables.tableBits input.val

def countedBits (input : Input) : List Bool := GraphCounterPrefix.output input.val

def words (H : BaseTable) (input : Input) (i : Nat) : List Bool :=
  GraphTables.tableBits (TableIteration.runTables H i input.val)

def count (input : Input) : Nat := GraphCounterPrefix.count input.val

noncomputable def lengthPolynomial : Polynomial Nat :=
  (GraphTableComplexity.encodingPolynomial 64).comp (PCPIterationMachine.sizePolynomial sizeFactor)

theorem inputBits_le_countedBits (input : Input) : (inputBits input).length ≤ (countedBits input).length := by
  simp only [inputBits, countedBits, GraphCounterPrefix.output, List.length_append]
  omega

theorem size_le_inputBits (input : Input) : size input ≤ (inputBits input).length := by
  have h := GraphTableComplexity.size_add_two_le_bits input.val
  unfold size inputBits
  omega

theorem count_le (input : Input) : count input ≤ (countedBits input).length + 1 :=
  (PCPIterationMachine.rounds_le (size input)).trans
    (Nat.add_le_add_right ((size_le_inputBits input).trans (inputBits_le_countedBits input)) 1)

theorem intermediate_size (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    size (TableIteration.run H i input) ≤ PCPIterationMachine.sizeEnvelope sizeFactor (size input) := by
  apply PCPIterationMachine.semanticSize_bound
    (fun j => size (TableIteration.run H j input)) sizeFactor (size input)
    sizeFactor_positive (Nat.le_succ _) _ i hi
  intro j _
  exact step_size H (TableIteration.run H j input)

theorem intermediate_bits (H : BaseTable) (input : Input) (i : Nat) (hi : i ≤ count input) :
    (words H input i).length ≤ lengthPolynomial.eval (countedBits input).length := by
  have hsize := intermediate_size H input i hi
  have hinput := (size_le_inputBits input).trans (inputBits_le_countedBits input)
  have heval := MachineComposition.natPolynomial_eval_mono
    (PCPIterationMachine.sizePolynomial sizeFactor) hinput
  rw [PCPIterationMachine.sizePolynomial_eval, PCPIterationMachine.sizePolynomial_eval] at heval
  have hs := hsize.trans heval
  have htable : (TableIteration.runTables H i input.val).vertices +
      (TableIteration.runTables H i input.val).darts ≤
        PCPIterationMachine.sizeEnvelope sizeFactor (countedBits input).length := by
    rw [← TableIteration.run_val]
    exact hs
  rw [lengthPolynomial, Polynomial.eval_comp, PCPIterationMachine.sizePolynomial_eval]
  exact GraphTableComplexity.bits_le_of_size_le _ htable

noncomputable def runtimePolynomial (bodyTime : Polynomial Nat) : Polynomial Nat :=
  (Polynomial.X + 1) * (bodyTime.comp lengthPolynomial + 2 * lengthPolynomial + 4) +
    2 * lengthPolynomial + 4

theorem runtimePolynomial_eval (bodyTime : Polynomial Nat) (N : Nat) :
    (runtimePolynomial bodyTime).eval N =
      (N + 1) * (bodyTime.eval (lengthPolynomial.eval N) + 2 * lengthPolynomial.eval N + 4) +
        2 * lengthPolynomial.eval N + 4 := by
  simp only [runtimePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_comp]

end IndependentSetsGames.Foundations.Complexity.GraphIterationBounds

namespace IndependentSetsGames.Foundations.PCP.RawInitialRows

open Target GraphTables RawInitialTables

abbrev Signs := Bool × Bool × Bool
abbrev Names := Nat × Nat × Nat

def clauseSigns {n : Nat} (c : Clause n) : Signs :=
  ((c)[0].positive, (c)[1].positive, (c)[2].positive)

def clauseNames {n : Nat} (c : Clause n) : Names :=
  ((c)[0].variableIndex.val, (c)[1].variableIndex.val, (c)[2].variableIndex.val)

def nameWord (names : Names) : Slot → Nat
  | .first => names.1
  | .second => names.2.1
  | .third => names.2.2

def decodedLabel (a : GraphTables.Label) : InitialGraph.Label :=
  AlphabetRetraction.decode64 (labelOrder.symm a)

def incidencePredicate (signs : Signs) (slot : Slot)
    (clauseLabel variableLabel : InitialGraph.Label) : Bool :=
  InitialGraph.variableValid variableLabel &&
    (((literalValue signs.1 clauseLabel.1 ||
      literalValue signs.2.1 clauseLabel.2.1) ||
      literalValue signs.2.2 clauseLabel.2.2) &&
      decide (answerAt (InitialGraph.toClauseAnswer clauseLabel) slot = variableLabel.1))

def relationPredicate (signs : Signs) (slot : Slot) :
    Bool → GraphTables.Label → GraphTables.Label → Bool
  | false, a, b => incidencePredicate signs slot (decodedLabel a) (decodedLabel b)
  | true, a, b => incidencePredicate signs slot (decodedLabel b) (decodedLabel a)

def relationWordsFor (signs : Signs) (slot : Slot) (orientation : Bool) : List Nat :=
  relationWords (relationOf (relationPredicate signs slot orientation))

@[simp] theorem relationWordsFor_length (signs : Signs) (slot : Slot) (orientation : Bool) :
    (relationWordsFor signs slot orientation).length = 4096 := by
  exact relationWords_length _

def incidenceWords (n i : Nat) (names : Names) (signs : Signs)
    (slot : Slot) (orientation : Bool) : List Nat :=
  [if orientation then nameWord names slot else n + i,
    6 * i + 2 * (slotOrder slot).val + (if orientation then 0 else 1)] ++
      relationWordsFor signs slot orientation

def clauseWords (n i : Nat) (names : Names) (signs : Signs) : List Nat :=
  incidenceWords n i names signs .first false ++
  incidenceWords n i names signs .first true ++
  incidenceWords n i names signs .second false ++
  incidenceWords n i names signs .second true ++
  incidenceWords n i names signs .third false ++
  incidenceWords n i names signs .third true

def dummyWords (n m : Nat) : List Nat :=
  [n + m, 6 * m] ++ List.replicate 4096 1

def orderedList {α : Type*} {n : Nat} (e : α ≃ Fin n) : List α :=
  List.ofFn e.symm

theorem orderedList_cast {α : Type*} {m n : Nat} (e : α ≃ Fin m) (h : m = n) :
    orderedList (e.trans (finCongr h)) = orderedList e := by
  subst n
  rfl

theorem orderedList_prod {α β : Type*} {m n : Nat}
    (e : α ≃ Fin m) (f : β ≃ Fin n) :
    orderedList ((e.prodCongr f).trans finProdFinEquiv) =
      (orderedList e).flatMap (fun a => (orderedList f).map (fun b => (a, b))) := by
  change List.ofFn (fun q : Fin (m * n) =>
    (e.symm (finProdFinEquiv.symm q).1, f.symm (finProdFinEquiv.symm q).2)) = _
  rw [List.ofFn_mul]
  simp only [orderedList, List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have h : (⟨i.val * n + j.val, by
      calc
        i.val * n + j.val < (i.val + 1) * n :=
          (Nat.add_lt_add_left j.isLt _).trans_eq (by rw [Nat.add_mul, Nat.one_mul])
        _ ≤ m * n := Nat.mul_le_mul_right _ i.isLt⟩ : Fin (m * n)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [h, Equiv.symm_apply_apply]
  rfl

theorem orderedList_sum {α β : Type*} {m n : Nat}
    (e : α ≃ Fin m) (f : β ≃ Fin n) :
    orderedList ((e.sumCongr f).trans finSumFinEquiv) =
      (orderedList e).map Sum.inl ++ (orderedList f).map Sum.inr := by
  change List.ofFn (fun q : Fin (m + n) =>
    (e.sumCongr f).symm (finSumFinEquiv.symm q)) = _
  rw [List.ofFn_add]
  change (List.ofFn (fun i : Fin m =>
    (e.sumCongr f).symm (finSumFinEquiv.symm (i.castAdd n)))) ++
    (List.ofFn (fun i : Fin n =>
      (e.sumCongr f).symm (finSumFinEquiv.symm (i.natAdd m)))) = _
  simp [orderedList, List.map_ofFn]
  rfl

def clauseDarts (F : Formula) (i : Fin F.clauses.length) : List (InitialGraph.Dart F) :=
  [.inl ((i, .first), false), .inl ((i, .first), true),
   .inl ((i, .second), false), .inl ((i, .second), true),
   .inl ((i, .third), false), .inl ((i, .third), true)]

theorem orderedList_dartOrder (F : Formula) :
    orderedList (dartOrder F) =
      (List.finRange F.clauses.length).flatMap (clauseDarts F) ++ [.inr ()] := by
  rw [dartOrder, orderedList_cast, orderedList_sum, orderedList_prod]
  rw [eventOrder, orderedList_prod]
  have hs : orderedList slotOrder = [.first, .second, .third] := rfl
  have hb : orderedList finTwoEquiv.symm = [false, true] := rfl
  have hu : orderedList unitOrder = [()] := rfl
  rw [hs, hb, hu]
  simp [orderedList, List.finRange, List.flatMap_assoc, List.map_flatMap,
    ]
  rfl

def rowFor (F : Formula) (d : InitialGraph.Dart F) :
    DartRow (F.«variables» + F.clauses.length + 1) (6 * F.clauses.length + 1) where
  tail := vertexOrder F (InitialGraph.tail F d)
  reverseIndex := dartOrder F (InitialGraph.reverse F d)
  relation := relationOf (fun a b => InitialGraph.predicate F d (decodedLabel a) (decodedLabel b))

theorem rowList_table (F : Formula) :
    rowList (table F) = (orderedList (dartOrder F)).map (rowFor F) := by
  simp only [rowList, table, ofEnumeratedGraph, ofGraph, graphRows, Vector.toList_ofFn,
    orderedList, List.map_ofFn]
  rfl

theorem rowWords_incidence (F : Formula) (i : Fin F.clauses.length)
    (slot : Slot) (orientation : Bool) :
    rowWords (rowFor F (.inl ((i, slot), orientation))) =
      incidenceWords F.«variables» i.val (clauseNames (clauseAt F i))
        (clauseSigns (clauseAt F i)) slot orientation := by
  have ht : (rowFor F (.inl ((i, slot), orientation))).tail.val =
      if orientation then nameWord (clauseNames (clauseAt F i)) slot else F.«variables» + i.val := by
    cases orientation <;> cases slot <;> rfl
  have hr : (rowFor F (.inl ((i, slot), orientation))).reverseIndex.val =
      6 * i.val + 2 * (slotOrder slot).val + (if orientation then 0 else 1) := by
    cases orientation <;> cases slot <;>
      simp [rowFor, InitialGraph.reverse, dartOrder, eventOrder, slotOrder, unitOrder,
        finProdFinEquiv, finSumFinEquiv, finTwoEquiv, Nat.mul_add,
        Nat.mul_comm, Nat.mul_left_comm, Nat.add_comm]
  have hp : (rowFor F (.inl ((i, slot), orientation))).relation =
      relationOf (relationPredicate (clauseSigns (clauseAt F i)) slot orientation) := by
    cases orientation <;> rfl
  unfold rowWords incidenceWords relationWordsFor
  rw [ht, hr, hp]

theorem rowWords_dummy (F : Formula) :
    rowWords (rowFor F (.inr ())) = dummyWords F.«variables» F.clauses.length := by
  have ht : (rowFor F (.inr ())).tail.val = F.«variables» + F.clauses.length := rfl
  have hr : (rowFor F (.inr ())).reverseIndex.val = 6 * F.clauses.length := by
    simp [rowFor, InitialGraph.reverse, dartOrder, unitOrder, finSumFinEquiv]
  have hp : (rowFor F (.inr ())).relation = relationOf (fun _ _ => true) := rfl
  have hw : relationWords (relationOf (fun _ _ => true)) = List.replicate 4096 1 := by
    unfold relationWords
    rw [relationOf, Vector.toList_ofFn, List.map_ofFn]
    exact List.ofFn_const 4096 1
  unfold rowWords dummyWords
  rw [ht, hr, hp, hw]

theorem clauseDarts_rowWords (F : Formula) (i : Fin F.clauses.length) :
    (clauseDarts F i).flatMap (fun d => rowWords (rowFor F d)) =
      clauseWords F.«variables» i.val (clauseNames (clauseAt F i))
        (clauseSigns (clauseAt F i)) := by
  simp [clauseDarts, rowWords_incidence, clauseWords, List.append_assoc]

theorem tableWords_eq (F : Formula) :
    tableWords (table F) =
      [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
      (List.finRange F.clauses.length).flatMap (fun i =>
        clauseWords F.«variables» i.val (clauseNames (clauseAt F i))
          (clauseSigns (clauseAt F i))) ++ dummyWords F.«variables» F.clauses.length := by
  rw [tableWords, rowList_table, orderedList_dartOrder]
  simp [List.flatMap_map, List.flatMap_append, List.flatMap_assoc, clauseDarts_rowWords,
    rowWords_dummy]

end IndependentSetsGames.Foundations.PCP.RawInitialRows

end OAI
