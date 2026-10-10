import Mathlib
import OAI.Analysis.MatrixSigning.Realization.ArrayRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine Matrix

variable {α β γ : Type*}

def singleton (ea : α → Word) : Realizes ea (listCode ea) (fun value => [value]) :=
  ((identity ea).both (constant ea (listCode ea) [])).then (consList ea)

def joinList (ea : α → Word) : Realizes (listCode (listCode ea)) (listCode ea) List.flatten :=
  (((constant (listCode (listCode ea)) (listCode ea) []).both
    (identity (listCode (listCode ea)))).then (appendList ea).fold).congr (by
      intro lists
      simpa using List.foldl_append_eq_append (l := lists) (f := id) (l' := ([] : List α)))

def Realizes.filterCtx {ec : γ → Word} {ea : α → Word} {p : γ×α → Bool}
    (r : Realizes (prodCode ec ea) boolCode p) :
    Realizes (prodCode ec (listCode ea)) (listCode ea)
      (fun input => input.2.filter (fun value => p (input.1,value))) :=
  let one := r.ite ((second ec ea).then (singleton ea))
    (constant (prodCode ec ea) (listCode ea) [])
  (one.mapCtx.then (joinList ea)).congr (by
    intro input
    induction input.2 with
    | nil => rfl
    | cons value values inductionHypothesis =>
      simp only [List.map_cons,List.flatten_cons]
      cases predicateValue : p (input.1,value) <;> simp_all)

def chooseFold (pred : α → Bool) (f : α → β) (xs : List α) (a : β) : β :=
  xs.foldr (fun value result => if pred value then f value else result) a

lemma chooseFold_find (pred : α → Bool) (f : α → β) (xs : List α) (a : β) :
    chooseFold pred f xs a = (xs.find? pred).elim a f := by
  induction xs with
  | nil => rfl
  | cons value values inductionHypothesis =>
    simp only [chooseFold,List.foldr_cons,List.find?_cons]
    cases predicateValue : pred value <;> simp_all [chooseFold]

def Realizes.findValue {ec : γ → Word} {ea : α → Word} {eb : β → Word}
    {p : γ×α → Bool} {f : γ×α → β}
    (test : Realizes (prodCode ec ea) boolCode p) (value : Realizes (prodCode ec ea) eb f) :
    Realizes (prodCode ec (prodCode eb (listCode ea))) eb
      (fun input => (input.2.2.find? (fun item => p (input.1,item))).elim input.2.1
        (fun item => f (input.1,item))) :=
  let context := first ec (prodCode eb (listCode ea))
  let rest := second ec (prodCode eb (listCode ea))
  let initial := rest.then (first eb (listCode ea))
  let values := rest.then (second eb (listCode ea))
  let previous := first (prodCode ec eb) ea
  let contextValue := (previous.then (first ec eb)).both (second (prodCode ec eb) ea)
  let body := (previous.then (first ec eb)).both
    ((contextValue.then test).ite (contextValue.then value) (previous.then (second ec eb)))
  let loop := ((context.both initial).both (values.then (reverseList ea))).then body.fold
  (loop.then (second ec eb)).congr (by
    intro input
    have foldPair : ∀ (items : List α) (initialValue : β),
        items.foldl (fun state item =>
          (state.1,if p (state.1,item) then f (state.1,item) else state.2))
            (input.1,initialValue) =
        (input.1,items.foldl (fun result item =>
          if p (input.1,item) then f (input.1,item) else result) initialValue) := by
      intro items
      induction items with
      | nil => intro initialValue; rfl
      | cons item items inductionHypothesis =>
        intro initialValue
        simpa only [List.foldl_cons] using inductionHypothesis _
    rw [foldPair,List.foldl_reverse]
    exact chooseFold_find _ _ _ _)

def zipDefault (f : α×β → γ) (a : α) (b : β) (p : List α×List β) : List γ :=
  (List.range p.1.length).map (fun i => f (p.1.getD i a,p.2.getD i b))

def Realizes.zipWith {ea : α → Word} {eb : β → Word} {ec : γ → Word}
    {f : α×β → γ} (r : Realizes (prodCode ea eb) ec f) (a : α) (b : β) :
    Realizes (prodCode (listCode ea) (listCode eb)) (listCode ec) (zipDefault f a b) :=
  let ctx := prodCode (listCode ea) (listCode eb)
  let ctxProjection := first ctx natCode
  let xs := ctxProjection.then (first (listCode ea) (listCode eb))
  let ys := ctxProjection.then (second (listCode ea) (listCode eb))
  let idx := second ctx natCode
  let xi := (idx.both xs).then (getD ea a)
  let yi := (idx.both ys).then (getD eb b)
  let each := (xi.both yi).then r
  ((identity ctx).both ((first (listCode ea) (listCode eb)).then (lengthList ea))).then each.tabulate

lemma getD_ofFn {n : ℕ} (f : Fin n → α) (i : Fin n) (a : α) :
    (List.ofFn f).getD i.val a=f i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma range_map_fin {n : ℕ} (f : ℕ → α) :
    (List.range n).map f=List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp at hi
    simp

lemma zipDefault_ofFn {n : ℕ} (f : α×β → γ) (a : α) (b : β)
    (x : Fin n → α) (y : Fin n → β) :
    zipDefault f a b (List.ofFn x,List.ofFn y)=List.ofFn (fun i => f (x i,y i)) := by
  unfold zipDefault
  rw [List.length_ofFn,range_map_fin]
  apply congrArg List.ofFn
  funext i
  rw [getD_ofFn,getD_ofFn]

abbrev vectorCode := listCode ratCode
abbrev matrixCode := listCode vectorCode
abbrev MatrixData := List (List ℚ)

def vectorAdd := (ratOp .add).zipWith 0 0

def vectorScaleBody : Realizes (prodCode ratCode ratCode) ratCode (fun p => p.1*p.2) :=
  ratOp .mul

def vectorScale := vectorScaleBody.mapCtx

def matrixAdd := vectorAdd.zipWith [] []

def matrixScale := vectorScale.mapCtx

def dotValue (p : List ℚ×List ℚ) : ℚ := (zipDefault (fun q : ℚ×ℚ => q.1*q.2) 0 0 p).sum

def dot : Realizes (prodCode vectorCode vectorCode) ratCode dotValue :=
  ((ratOp .mul).zipWith 0 0).then sumRationals

def matVecValue (p : MatrixData×List ℚ) : List ℚ := p.1.map (fun row => dotValue (row,p.2))

def matVec : Realizes (prodCode matrixCode vectorCode) vectorCode matVecValue :=
  let swap := (second matrixCode vectorCode).both (first matrixCode vectorCode)
  let rowDot := ((second vectorCode vectorCode).both (first vectorCode vectorCode)).then dot
  swap.then rowDot.mapCtx

def quadraticValue (p : List ℚ×MatrixData) : ℚ := dotValue (p.1,matVecValue (p.2,p.1))

def quadratic : Realizes (prodCode vectorCode matrixCode) ratCode quadraticValue :=
  let v := first vectorCode matrixCode
  let m := second vectorCode matrixCode
  (v.both ((m.both v).then matVec)).then dot

def matrixData {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℚ) : MatrixData :=
  List.ofFn (fun i => List.ofFn (M i))

lemma vectorAdd_ofFn {n : ℕ} (x y : Fin n → ℚ) :
    zipDefault (fun p : ℚ×ℚ => p.1+p.2) 0 0 (List.ofFn x,List.ofFn y)=List.ofFn (x+y) :=
  zipDefault_ofFn _ _ _ _ _

lemma matrixAdd_data {n m : ℕ} (A B : Matrix (Fin n) (Fin m) ℚ) :
    zipDefault (zipDefault (fun p : ℚ×ℚ => p.1+p.2) 0 0) [] [] (matrixData A,matrixData B)=
      matrixData (A+B) := by
  rw [matrixData,matrixData,zipDefault_ofFn]
  simp only [vectorAdd_ofFn]
  rfl

lemma matrixScale_data {n m : ℕ} (q : ℚ) (A : Matrix (Fin n) (Fin m) ℚ) :
    (matrixData A).map (fun row => row.map (fun x => q*x))=matrixData (q • A) := by
  simp only [matrixData,List.map_ofFn,Function.comp_def]
  rfl

lemma dot_ofFn {n : ℕ} (x y : Fin n → ℚ) : dotValue (List.ofFn x,List.ofFn y)=dotProduct x y := by
  unfold dotValue
  rw [zipDefault_ofFn,List.sum_ofFn]
  rfl

lemma matVec_data {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℚ) (v : Fin m → ℚ) :
    matVecValue (matrixData A,List.ofFn v)=List.ofFn (A *ᵥ v) := by
  simp only [matVecValue,matrixData,List.map_ofFn,Function.comp_def,dot_ofFn]
  rfl

lemma quadratic_data {n : ℕ} (v : Fin n → ℚ) (A : Matrix (Fin n) (Fin n) ℚ) :
    quadraticValue (List.ofFn v,matrixData A)=dotProduct v (A *ᵥ v) := by
  rw [quadraticValue,matVec_data,dot_ofFn]

end CurrentKS.Realization

end

end OAI
