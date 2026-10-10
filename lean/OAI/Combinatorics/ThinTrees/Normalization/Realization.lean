import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialCurvature
import OAI.Analysis.MatrixSigning.Complexity.PolynomialExplicit
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFind
import OAI.Analysis.MatrixSigning.Complexity.PolynomialMatrixFold
import OAI.Analysis.MatrixSigning.Complexity.PolynomialValueQuery
import OAI.Analysis.MatrixSigning.Realization.VarianceRealization
import OAI.Combinatorics.ThinTrees.Normalization.Algorithm

namespace OAI

/-! Normalization realization. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {β : Type*}

def selectFlagged (eb : β → Word) :
    Realizes (prodCode eb (listCode (prodCode boolCode eb))) eb
      (fun p => (p.2.find? Prod.fst).elim p.1 Prod.snd) :=
  let ec := prodCode boolCode eb
  let ctx := first eb (listCode ec)
  let test := (second eb ec).then (first boolCode eb)
  let value := (second eb ec).then (second boolCode eb)
  ((ctx.both (identity (prodCode eb (listCode ec)))).then
    (test.findValue value)).congr (fun _ => rfl)

instance poly_selectFlagged (eb : β → Word) : PolyTime (selectFlagged eb) := by
  unfold selectFlagged
  infer_instance

lemma find_map_flagged {α β : Type*} (xs : List α) (p : α → Bool)
    (f : α → β) (b : β) :
    (((xs.map fun a => (p a,f a)).find? Prod.fst).elim b Prod.snd)=
      (xs.find? p).elim b f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,List.find?_cons]
    cases h : p a <;> simp_all
end CurrentKS.Realization

namespace AlgorithmicThinTrees.Normalization.Stack
open CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open Matrix
local notation "X" => NaturalPolynomial.variable

structure Params where
  d : ℕ
  m : ℕ
  q : ℕ
  t : ℚ
  v : Fin m → Fin d → ℚ

abbrev paramsDataCode :=
  prodCode natCode (prodCode natCode (prodCode ratCode matrixCode))
def Params.data (p : Params) := (p.d,(p.q,(p.t,matrixData p.v)))
def paramsCode (p : Params) : Word := paramsDataCode p.data
abbrev view : Realizes paramsCode paramsDataCode Params.data :=
  (identity paramsDataCode).reindex paramsCode Params.data (fun _ => rfl)
private instance poly_view : PolyTime view := by
  unfold view
  apply poly_reindex

abbrev dim := view.then (first natCode (prodCode natCode (prodCode ratCode matrixCode)))
abbrev rest := view.then (second natCode (prodCode natCode (prodCode ratCode matrixCode)))
abbrev count := rest.then (first natCode (prodCode ratCode matrixCode))
abbrev tail := rest.then (second natCode (prodCode ratCode matrixCode))
abbrev factor := tail.then (first ratCode matrixCode)
abbrev columns := tail.then (second ratCode matrixCode)
def numColumns : Realizes paramsCode natCode Params.m :=
  (columns.then (lengthList vectorCode)).congr (by
    intro p
    exact List.length_ofFn)
instance poly_numColumns : PolyTime numColumns := by
  unfold numColumns
  apply poly_congr

def outer : Realizes vectorCode matrixCode
    (fun xs : List ℚ => xs.map (fun q => xs.map (fun r => q*r))) :=
  let one := ((second vectorCode ratCode).both (first vectorCode ratCode)).then vectorScale
  ((identity vectorCode).both (identity vectorCode)).then one.mapCtx
instance poly_outer : PolyTime outer := by
  unfold outer
  infer_instance
lemma outer_data {d : ℕ} (v : Fin d → ℚ) :
    (List.ofFn v).map (fun q => (List.ofFn v).map (fun r => q*r))=
      matrixData (vecMulVec v v) := by
  simp only [List.map_ofFn,Function.comp_def,matrixData]
  rfl

structure State where
  params : Params
  scales : Fin params.m → ℚ

def stateCode (s : State) : Word :=
  prodCode paramsCode vectorCode (s.params,List.ofFn s.scales)
abbrev stateView : Realizes stateCode (prodCode paramsCode vectorCode)
    (fun s => (s.params,List.ofFn s.scales)) :=
  (identity (prodCode paramsCode vectorCode)).reindex stateCode
    (fun s => (s.params,List.ofFn s.scales)) (fun _ => rfl)
private instance poly_stateView : PolyTime stateView := by
  unfold stateView
  apply poly_reindex

abbrev params := stateView.then (first paramsCode vectorCode)
abbrev scales := stateView.then (second paramsCode vectorCode)

def gram : Realizes stateCode matrixCode
    (fun s => matrixData (covariance s.params.v (weights s.scales))) :=
  (((params.then dim).both
    ((scales.then ((identity ratCode).pow 2).map).both
      ((params.then columns).then outer.map))).then weightedSum).congr (by
        intro s
        change weightedSumData (s.params.d,
          ((List.ofFn s.scales).map (fun q => q^2),
            (matrixData s.params.v).map (fun xs => xs.map (fun q => xs.map (fun r => q*r)))))=_
        simp only [matrixData,List.map_ofFn,Function.comp_def]
        change weightedSumData (s.params.d,
          (List.ofFn (weights s.scales),List.ofFn (fun e => matrixData (vecMulVec (s.params.v e) (s.params.v e)))))=_
        exact weightedSum_data _ _)
instance poly_gram : PolyTime gram := by
  unfold gram
  infer_instance

abbrev Column := Σ s : State, Fin s.params.m
abbrev columnCode := finFamilyCode stateCode (fun s : State => s.params.m)
abbrev colState : Realizes columnCode stateCode (fun x : Column => x.1) := familyFirst
abbrev colIndex : Realizes columnCode natCode (fun x : Column => x.2.val) := familyIndex
abbrev colParams := colState.then params

def column : Realizes columnCode vectorCode (fun x => List.ofFn (x.1.params.v x.2)) :=
  ((colIndex.both (colParams.then columns)).then (getD vectorCode [])).congr (by
    intro x
    exact getD_ofFn _ _ _)
def scale : Realizes columnCode ratCode (fun x => x.1.scales x.2) :=
  ((colIndex.both (colState.then scales)).then (getD ratCode 0)).congr (by
    intro x
    exact getD_ofFn _ _ _)
instance poly_column : PolyTime column := by unfold column; apply poly_congr
instance poly_scale : PolyTime scale := by unfold scale; infer_instance

def thresholdProgram : Realizes paramsCode ratCode (fun p => threshold p.q p.t) :=
  let c (q : ℚ) := constant paramsCode ratCode q
  ((c 1).div (count.then natToRat)).add
    ((c 4).mul ((c 1).sub (factor.pow 2)))
instance poly_thresholdProgram : PolyTime thresholdProgram := by
  have hfactor : PolyTime factor := by
    unfold factor
    apply poly_then
  unfold thresholdProgram
  refine @poly_add _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · refine @poly_mul _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · refine @poly_sub _ _ _ _ _ _ ?_ ?_
      · infer_instance
      · exact hfactor.pow 2

def testProgram : Realizes columnCode matrixObjectCode
    (fun x => ⟨x.1.params.d,testMatrix x.1.params.q x.1.params.t
      x.1.params.v x.1.scales x.2⟩) :=
  let firstPart := (((colParams.then thresholdProgram).both (colState.then gram)).then matrixScale)
  let secondPart := (((scale.pow 2).both (column.then outer)).then matrixScale)
  ((colParams.then dim).both ((firstPart.both secondPart).then matrixSub)).changeOutput
    matrixObjectCode (fun x => ⟨x.1.params.d,testMatrix x.1.params.q x.1.params.t
      x.1.params.v x.1.scales x.2⟩) (by
        intro x
        simp only [matrixScale_data,outer_data]
        change prodCode natCode matrixCode (x.1.params.d,
          matrixSubData
            (matrixData (threshold x.1.params.q x.1.params.t •
              covariance x.1.params.v (weights x.1.scales)),
            matrixData ((x.1.scales x.2)^2 • vecMulVec (x.1.params.v x.2) (x.1.params.v x.2))))=_
        rw [matrixSub_data]
        rfl)
instance poly_testProgram : PolyTime testProgram := by
  unfold testProgram
  infer_instance

def isHeavy : Realizes columnCode boolCode
    (fun x => (KS.W17.rationalNegativeWitness x.1.params.d
      (testMatrix x.1.params.q x.1.params.t x.1.params.v x.1.scales x.2)).isSome) :=
  ((testProgram.then isPSD).ite (constant columnCode boolCode false)
    (constant columnCode boolCode true)).congr (by
      intro x
      cases h : KS.W17.rationalNegativeWitness x.1.params.d
        (testMatrix x.1.params.q x.1.params.t x.1.params.v x.1.scales x.2) <;> simp)
instance poly_isHeavy : PolyTime isHeavy := by unfold isHeavy; infer_instance

def updated : Realizes columnCode vectorCode
    (fun x => List.ofFn (Function.update x.1.scales x.2 (x.1.params.t*x.1.scales x.2))) :=
  (((colState.then scales).both (colIndex.both ((colParams.then factor).mul scale))).then
    updateVector).congr (fun _ => update_data _ _ _)
instance poly_updated : PolyTime updated := by unfold updated; apply poly_congr

def newScales : Realizes stateCode vectorCode
    (fun s => List.ofFn (advance s.params.q s.params.t s.params.v s.scales)) :=
  ((scales.both ((isHeavy.both updated).tabulateFin (params.then numColumns))).then
    (selectFlagged vectorCode)).congr (by
      intro s
      dsimp only
      rw [List.ofFn_eq_map (f := fun e =>
        ((KS.W17.rationalNegativeWitness s.params.d
          (testMatrix s.params.q s.params.t s.params.v s.scales e)).isSome,
          List.ofFn (Function.update s.scales e (s.params.t*s.scales e)))),find_map_flagged]
      unfold advance heavy
      cases h : (List.finRange s.params.m).find? (fun e =>
        (KS.W17.rationalNegativeWitness s.params.d
          (testMatrix s.params.q s.params.t s.params.v s.scales e)).isSome) <;> rfl)
instance poly_newScales : PolyTime newScales := by unfold newScales; infer_instance

def State.next (s : State) : State :=
  ⟨s.params,advance s.params.q s.params.t s.params.v s.scales⟩
def step : Realizes stateCode stateCode State.next :=
  (params.both newScales).changeOutput stateCode State.next (fun _ => rfl)
instance poly_step : PolyTime step := by unfold step; apply poly_changeOutput

lemma next_iterate (s : State) (n : ℕ) :
    State.next^[n] s=⟨s.params,(advance s.params.q s.params.t s.params.v)^[n] s.scales⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    change State.mk s.params (advance _ _ _ _) = State.mk s.params _
    rw [Function.iterate_succ_apply']

lemma advance_iterate_parts (p : Params) (s : Fin p.m → ℚ) {b : ℕ}
    (ht : QParts b p.t) (hs : ∀i,QParts b (s i)) (k : ℕ) :
    ∀i,QParts (b+k*b) ((advance p.q p.t p.v)^[k] s i) := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    intro i
    rw [Function.iterate_succ_apply']
    rw [advance]
    cases hh : heavy p.q p.t p.v ((advance p.q p.t p.v)^[k] s) with
    | none =>
      exact (ih i).mono (show b+k*b ≤ b+(k+1)*b by simp only [Nat.add_mul,Nat.one_mul]; omega)
    | some j =>
      simp only [Option.elim_some]
      by_cases h : i=j
      · subst i
        simpa only [Function.update_self,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht.mul (ih j)
      · simpa only [Function.update_of_ne h] using
          (ih i).mono (show b+k*b ≤ b+(k+1)*b by simp only [Nat.add_mul,Nat.one_mul]; omega)

instance size_step : IterateSize step := by
  refine ⟨⟨100*(X+1)^3,?_⟩⟩
  intro s k
  let L := (stateCode s).length
  have hp : (paramsCode s.params).length≤L := le_prodCode_left (s.params,List.ofFn s.scales)
  have hy : (vectorCode (List.ofFn s.scales)).length≤L := le_prodCode_right (s.params,List.ofFn s.scales)
  have ht : QParts L s.params.t := (qparts_length _).mono
    (((le_prodCode_left (s.params.t,matrixData s.params.v)).trans
      (le_prodCode_right (s.params.q,(s.params.t,matrixData s.params.v)))).trans
        ((le_prodCode_right s.params.data).trans hp))
  have hs : ∀i,QParts L (s.scales i) := by
    intro i
    exact (qparts_length _).mono
      ((mem_length_le_code (List.ofFn s.scales) (List.mem_ofFn.mpr ⟨i,rfl⟩)).trans hy)
  have hm : s.params.m≤L := by
    simpa only [List.length_ofFn] using (list_length_le_code ratCode (List.ofFn s.scales)).trans hy
  have hlen := listCode_length_bound
    (List.ofFn ((advance s.params.q s.params.t s.params.v)^[k] s.scales)) (4*(L+k*L)+7) (by
      intro q hq
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
      exact (advance_iterate_parts s.params s.scales ht hs k i).length)
  rw [List.length_ofFn] at hlen
  have hlen' := hlen.trans (Nat.mul_le_mul_right _ hm)
  change (stateCode (State.next^[k] s)).length≤100*(L+k+1)^3
  rw [next_iterate]
  change (prodCode paramsCode vectorCode
    (s.params,List.ofFn ((advance s.params.q s.params.t s.params.v)^[k] s.scales))).length≤_
  rw [prodCode_length]
  dsimp only
  change (vectorCode (List.ofFn ((advance s.params.q s.params.t s.params.v)^[k] s.scales))).length≤_ at hlen'
  have hL : L≤L+k+1 := by omega
  have hk : k≤L+k+1 := by omega
  have hLL := Nat.mul_le_mul hL hL
  have hkLL := Nat.mul_le_mul hk hLL
  nlinarith

def initial : Realizes paramsCode stateCode (fun p => ⟨p,fun _ => 1⟩) :=
  ((identity paramsCode).both
    (((constant paramsCode ratCode 1).both numColumns).then (replicateList ratCode))).changeOutput
      stateCode (fun p => ⟨p,fun _ => 1⟩) (by
        intro p
        change prodCode paramsCode vectorCode (p,List.replicate p.m 1)=
          prodCode paramsCode vectorCode (p,List.ofFn (fun _ : Fin p.m => (1:ℚ)))
        rw [List.ofFn_const])
instance poly_initial : PolyTime initial := by unfold initial; infer_instance

def run : Realizes (prodCode natCode paramsCode) vectorCode
    (fun a => List.ofFn (scalesAt a.2.q a.2.t a.2.v a.1)) :=
  ((((first natCode paramsCode).both ((second natCode paramsCode).then initial)).then
    step.iterate).then scales).congr (by
      intro a
      rw [next_iterate]
      rfl)
instance poly_run : PolyTime run := by unfold run; infer_instance

def unaryPow (k : ℕ) : Realizes natCode natCode (fun n => n^k) :=
  match k with
  | 0 => (constant natCode natCode 1).congr (fun _ => rfl)
  | k+1 => (((unaryPow k).both (identity natCode)).then natMul).congr
      (fun _ => (pow_succ _ _).symm)
instance poly_unaryPow (k : ℕ) : PolyTime (unaryPow k) := by
  induction k with
  | zero => unfold unaryPow; apply poly_congr
  | succ k ih => unfold unaryPow; infer_instance

abbrev fixedCode := prodCode paramsCode natCode
abbrev fixedParams := first paramsCode natCode
abbrev fixedR := second paramsCode natCode

def multiplierProgram : Realizes natCode ratCode multiplier :=
  let c (q : ℚ) := constant natCode ratCode q
  (c 1).sub ((c 1).div ((c 16).mul (natToRat.pow 2)))
instance poly_multiplierProgram : PolyTime multiplierProgram := by
  unfold multiplierProgram; apply poly_sub

def fixedStepParams (a : Params×ℕ) : Params :=
  ⟨a.1.d,a.1.m,a.1.q,multiplier a.2,a.1.v⟩
def fixedStep : Realizes fixedCode paramsCode fixedStepParams :=
  ((fixedParams.then dim).both ((fixedParams.then count).both
    ((fixedR.then multiplierProgram).both (fixedParams.then columns)))).changeOutput
      paramsCode fixedStepParams (fun _ => rfl)
instance poly_fixedStep : PolyTime fixedStep := by unfold fixedStep; apply poly_changeOutput

def lengthProgram : Realizes fixedCode natCode
    (fun a => normalizationLength a.1.m a.2) :=
  let c (n : ℕ) := constant fixedCode natCode n
  let m := fixedParams.then numColumns
  ((((((c 2).both m).then natMul).then natSucc).both (c 256)).then natMul).both
    (fixedR.then (unaryPow 4)) |>.then natMul
instance poly_lengthProgram : PolyTime lengthProgram := by unfold lengthProgram; apply poly_then

def normalized : Realizes fixedCode vectorCode
    (fun a => List.ofFn (normalizedScales a.1.q a.2 a.1.v)) :=
  (lengthProgram.both fixedStep).then run
instance poly_normalized : PolyTime normalized := by unfold normalized; apply poly_then

end AlgorithmicThinTrees.Normalization.Stack
end

end OAI
