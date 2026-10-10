import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.RoundComputation
import OAI.Combinatorics.IndependentSets.Encoding.BinaryNormalize
import OAI.Combinatorics.IndependentSets.Reduction.IndexedBlocks
import OAI.Combinatorics.IndependentSets.Machines.MachineLazyTableRuntime

namespace OAI

namespace LargeIndependentSets.PCPGapMachine
open IndependentSetsGames.Foundations
open Complexity PCP

noncomputable def round (H : RoundTables.BaseTable) :=
  RoundComputation.tablePolynomialTime H (PreprocessingRuntime.tablePolynomialTime H)

lemma round_finiteAlphabet (H : RoundTables.BaseTable) :
    MachineFiniteAlphabet.FiniteAlphabet (round H).tm :=
  RoundComputation.tablePolynomialTime_finite_alphabet H
    (PreprocessingRuntime.tablePolynomialTime H) (PreprocessingRuntime.finiteAlphabet H)

noncomputable def certificate (H : RoundTables.BaseTable) :
    Turing.TM2ComputableInPolyTime Complexity.formulaBits Complexity.formulaBits
      (TableIteration.gapMap H) :=
  MachineTableIteration.gapMapCertificate H (round H)

lemma finiteAlphabet (H : RoundTables.BaseTable) :
    MachineFiniteAlphabet.FiniteAlphabet (certificate H).tm :=
  TableIterationFiniteAlphabet.gapMap H (round H) (round_finiteAlphabet H)
end LargeIndependentSets.PCPGapMachine
namespace LargeIndependentSets.BinaryNormalize
open BinarySyntax BinaryNames
open IndependentSetsGames.Foundations
open IndependentSetsCut.CounterMachine
open scoped BigOperators

@[simp] lemma annotated_input (s : List Bool) : (annotated s).input = s :=
  FiniteScan.iterate_input _ _ _ _

def eventCode : Option Mark → ℕ
  | none => 0
  | some .empty => 1
  | some (.first r) => 2+r.val

def sourcePosition (s : List Bool) (p r j : ℕ) : ℕ :=
  if j=1 ∧ 1 ≤ r then next s p else
    if j=2 ∧ 2 ≤ r then next s (next s p) else p

def blockValue (s : List Bool) (p i : ℕ) : ℕ :=
  let tag := eventCode (eventAt s p)
  let slot := (i/2)%3
  if 2 ≤ tag ∧ i<6 then
    let pos := sourcePosition s p (tag-2) slot
    if i%2=0 then key s pos else if raw s pos then 1 else 0
  else if i%2=0 then 0
  else if tag=1 then (if 6 ≤ i then 1 else 0)
  else if slot=1 then 0 else 1

lemma blockValue_spec (s : List Bool) (p : ℕ) :
    (List.range 12).map (blockValue s p) =
      Complexity.clauseWords (row s p false) ++ Complexity.clauseWords (row s p true) := by
  cases he : eventAt s p with
  | none => simp [blockValue,he,eventCode,row,tautology,constant,triple,
      Complexity.clauseWords,Complexity.literalWords,List.range_succ]
  | some e =>
    cases e with
    | empty => simp [blockValue,he,eventCode,row,unitClause,constant,triple,
        Complexity.clauseWords,Complexity.literalWords,List.range_succ]
    | first r =>
      fin_cases r <;> simp [blockValue,he,eventCode,row,sourceClause,sourcePosition,dense,
        tautology,constant,triple,Complexity.clauseWords,Complexity.literalWords,List.range_succ]

lemma clauses_length (s : List Bool) : (normalize s).clauses.length=2*s.length := by
  simp [normalize,List.length_flatMap,Nat.mul_comm]

def tableCount (s : List Bool) : ℕ := 2+12*s.length

def tableValue (s : List Bool) (w : ℕ) : ℕ :=
  if w=0 then s.length+1 else if w=1 then 2*s.length
  else blockValue s ((w-2)/12) ((w-2)%12)

lemma tableValue_spec (s : List Bool) :
    (List.range (tableCount s)).map (tableValue s) = Complexity.formulaWords (normalize s) := by
  rw [tableCount,List.range_add,List.map_append]
  have h0 : (List.range 2).map (tableValue s)=[s.length+1,2*s.length] := by
    simp [List.range_succ,tableValue]
  rw [h0]
  have h1 : ((List.range (12*s.length)).map (fun x => 2+x)).map (tableValue s) =
      (List.range (12*s.length)).map (fun i => blockValue s (i/12) (i%12)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    simp [tableValue,show 2+i≠1 by omega]
  rw [h1,IndexedBlocks.range_blocks _ 12 (by omega)]
  unfold Complexity.formulaWords
  rw [clauses_length]
  congr 1
  change (List.range s.length).flatMap (fun p => (List.range 12).map (blockValue s p)) =
    ((List.range s.length).flatMap (fun p => [row s p false,row s p true])).flatMap
      (@Complexity.clauseWords (varCount s))
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro p _
  simpa using blockValue_spec s p

lemma encodeWords_flatMap (xs : List ℕ) :
    Complexity.encodeWords xs=xs.flatMap (fun v => List.replicate v true++[false]) := by
  induction xs with
  | nil => rfl
  | cons v xs ih => simp [Complexity.encodeWords,Complexity.encodeWord,ih]

lemma tableWords_spec (s : List Bool) :
    UnaryTables.words (tableValue s) (tableCount s) = Complexity.formulaBits (normalize s) := by
  rw [UnaryTables.words,tableValue_spec,Complexity.formulaBits,encodeWords_flatMap]

def finiteTableExpr {m : ℕ} (f : Fin m → Bool → ℕ) (q b : Expr) : Expr :=
  Expr.listSum (List.finRange m) (fun i => .mul (Expr.equal q (.const i.val))
    (Expr.cond b (.const (f i true)) (.const (f i false))))

lemma finiteTableExpr_eval {m : ℕ} (f : Fin m → Bool → ℕ) (q b : Expr)
    (s : List Bool) (a : ℕ → ℕ) (i : Fin m) (c : Bool)
    (hq : q.eval s a=i.val) (hb : b.eval s a=if c then 1 else 0) :
    (finiteTableExpr f q b).eval s a=f i c := by
  simp only [finiteTableExpr,Expr.listSum_eval,Expr.eval,Expr.equal_eval,Expr.cond_eval,hq,hb]
  cases c <;> simp only [Bool.false_eq_true,↓reduceIte,ne_eq,not_true_eq_false,
    one_ne_zero,not_false_eq_true]
  all_goals
    rw [← List.ofFn_eq_map,List.sum_ofFn]
    simp [Fin.val_inj]

noncomputable def tagExpr (p : Expr) : Expr :=
  finiteTableExpr (fun q b => eventCode (event (phaseEquiv.symm q) b))
    (FiniteScan.historyExpr p) (rawExpr p)

lemma tagExpr_eval (s : List Bool) (p : Expr) (a : ℕ → ℕ)
    (hp : p.eval (annotated s).bits a ≤ s.length) :
    (tagExpr p).eval (annotated s).bits a=eventCode (eventAt s (p.eval (annotated s).bits a)) := by
  unfold tagExpr
  rw [finiteTableExpr_eval _ _ _ _ _
    (phaseEquiv (run .headerMark (s.take (p.eval (annotated s).bits a))))
    (raw s (p.eval (annotated s).bits a))]
  · simp [eventAt]
  · simp only [FiniteScan.historyExpr_eval,FiniteScan.nExpr_eval,annotated_input]
    have hr := FiniteScan.read_history (annotated s) (p.eval (annotated s).bits a)
      (by simpa only [annotated_input] using hp)
    simpa only [annotated_input,annotated_history _ _ hp] using hr
  · simpa only [annotated_input] using rawExpr_eval (annotated s) p a

def sourcePositionExpr (p r j : Expr) : Expr :=
  Expr.cond (.mul (Expr.equal j (.const 1)) (Expr.le (.const 1) r)) (nextExpr p)
    (Expr.cond (.mul (Expr.equal j (.const 2)) (Expr.le (.const 2) r))
      (nextExpr (nextExpr p)) p)

lemma sourcePositionExpr_eval {m : ℕ} (s : FiniteScan.State m) (p r j : Expr) (a : ℕ → ℕ) :
    (sourcePositionExpr p r j).eval s.bits a =
      sourcePosition s.input (p.eval s.bits a) (r.eval s.bits a) (j.eval s.bits a) := by
  simp only [sourcePositionExpr,Expr.cond_eval,Expr.eval,Expr.equal_eval,Expr.le_eval,
    nextExpr_eval,sourcePosition]
  by_cases h1 : j.eval s.bits a=1 <;> by_cases h2 : j.eval s.bits a=2 <;>
    by_cases hr1 : 1 ≤ r.eval s.bits a <;> by_cases hr2 : 2 ≤ r.eval s.bits a <;>
    simp [h1,h2,hr1,hr2]

def blockExpr (p i tag : Expr) : Expr :=
  let slot := Expr.remainder (Expr.quotient i (.const 2)) (.const 3)
  let pos := sourcePositionExpr p (.sub tag (.const 2)) slot
  Expr.cond (.mul (Expr.le (.const 2) tag) (Expr.lt i (.const 6)))
    (Expr.cond (Expr.equal (Expr.remainder i (.const 2)) (.const 0)) (keyExpr pos) (rawExpr pos))
    (Expr.cond (Expr.equal (Expr.remainder i (.const 2)) (.const 0)) (.const 0)
      (Expr.cond (Expr.equal tag (.const 1)) (Expr.le (.const 6) i)
        (Expr.cond (Expr.equal slot (.const 1)) (.const 0) (.const 1))))

lemma blockExpr_eval (s : List Bool) (p i : Expr) (a : ℕ → ℕ)
    (hp : p.eval (annotated s).bits a  ≤  s.length) :
    (blockExpr p i (tagExpr p)).eval (annotated s).bits a=
      blockValue s (p.eval (annotated s).bits a) (i.eval (annotated s).bits a) := by
  simp only [blockExpr,Expr.cond_eval,Expr.eval,Expr.le_eval,Expr.lt_eval,Expr.equal_eval,
    tagExpr_eval s p a hp,keyExpr_eval,rawExpr_eval,sourcePositionExpr_eval,
    Expr.quotient_eval,Expr.remainder_eval,annotated_input]
  unfold blockValue
  by_cases ht : 2 ≤ eventCode (eventAt s (p.eval (annotated s).bits a)) <;>
    by_cases hi : i.eval (annotated s).bits a < 6 <;>
    by_cases hr : i.eval (annotated s).bits a % 2 = 0 <;>
    by_cases he : eventCode (eventAt s (p.eval (annotated s).bits a)) = 1 <;>
    by_cases hs : (i.eval (annotated s).bits a / 2) % 3 = 1 <;>
    simp [ht,hi,hr,he,hs,show (6 ≤ i.eval (annotated s).bits a) ↔
      ¬i.eval (annotated s).bits a < 6 by omega]

def countExpr : Expr := .add (.const 2) (.mul (.const 12) FiniteScan.nExpr)
noncomputable def valueExpr : Expr :=
  let p := Expr.quotient (.sub (.arg 0) (.const 2)) (.const 12)
  let i := Expr.remainder (.sub (.arg 0) (.const 2)) (.const 12)
  Expr.cond (Expr.equal (.arg 0) (.const 0)) (.add FiniteScan.nExpr (.const 1))
    (Expr.cond (Expr.equal (.arg 0) (.const 1)) (.mul (.const 2) FiniteScan.nExpr)
      (blockExpr p i (tagExpr p)))

lemma countExpr_eval (s : List Bool) (a : ℕ → ℕ) :
    countExpr.eval (annotated s).bits a=tableCount s := by
  simp [countExpr,Expr.eval,tableCount]

lemma valueExpr_eval (s : List Bool) (w : ℕ) (hw : w<tableCount s) :
    valueExpr.eval (annotated s).bits (fun _ => w)=tableValue s w := by
  have hp : (w-2)/12 ≤ s.length := by unfold tableCount at hw; omega
  have hb := blockExpr_eval s (Expr.quotient (.sub (.arg 0) (.const 2)) (.const 12))
    (Expr.remainder (.sub (.arg 0) (.const 2)) (.const 12)) (fun _ => w) (by simpa [Expr.eval] using hp)
  simp only [valueExpr,Expr.cond_eval,Expr.equal_eval,Expr.eval,hb,FiniteScan.nExpr_eval,annotated_input,Expr.quotient_eval,Expr.remainder_eval]
  by_cases h0 : w=0 <;> by_cases h1 : w=1 <;> simp [tableValue,h0,h1]

lemma serializer_spec (s : List Bool) :
    UnaryTables.words (fun w => valueExpr.eval (annotated s).bits (fun _ => w))
      (countExpr.eval (annotated s).bits (fun _ => 0))=Complexity.formulaBits (normalize s) := by
  rw [countExpr_eval,← tableWords_spec]
  exact UnaryTables.words_congr (valueExpr_eval s)

noncomputable def serializer : Turing.TM2ComputableInPolyTime
    (fun s => (annotated s).bits) Complexity.formulaBits normalize :=
  UnaryTables.encodedComputer _ _ _ countExpr valueExpr serializer_spec

lemma serializer_finiteAlphabet : Complexity.MachineFiniteAlphabet.FiniteAlphabet serializer.tm :=
  UnaryTables.encodedComputer_finiteAlphabet _ _ _ _ _ _

noncomputable def annotator : Turing.TM2ComputableInPolyTime
    (id : List Bool → List Bool) (fun s => (annotated s).bits) id where
  tm := BinarySyntax.certificate.tm
  inputAlphabet := BinarySyntax.certificate.inputAlphabet
  outputAlphabet := BinarySyntax.certificate.outputAlphabet
  time := BinarySyntax.certificate.time
  outputsFun := BinarySyntax.certificate.outputsFun

noncomputable def certificate : Turing.TM2ComputableInPolyTime
    (id : List Bool → List Bool) Complexity.formulaBits normalize :=
  Complexity.MachineSequential.composeBits annotator serializer

lemma finiteAlphabet : Complexity.MachineFiniteAlphabet.FiniteAlphabet certificate.tm :=
  Complexity.MachineFiniteAlphabet.composeBits annotator serializer
    BinarySyntax.finiteAlphabet serializer_finiteAlphabet

noncomputable def gapCertificate (H : PCP.RoundTables.BaseTable) :
    Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) Complexity.formulaBits
      (fun s => PCP.TableIteration.gapMap H (normalize s)) :=
  Complexity.MachineSequential.composeBits certificate (PCPGapMachine.certificate H)

lemma gap_finiteAlphabet (H : PCP.RoundTables.BaseTable) :
    Complexity.MachineFiniteAlphabet.FiniteAlphabet (gapCertificate H).tm :=
  Complexity.MachineFiniteAlphabet.composeBits certificate (PCPGapMachine.certificate H)
    finiteAlphabet (PCPGapMachine.finiteAlphabet H)

end LargeIndependentSets.BinaryNormalize

end OAI
