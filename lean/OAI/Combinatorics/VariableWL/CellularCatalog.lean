import OAI.Combinatorics.VariableWL.CircuitCatalog

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5

namespace VariableWL.CircuitCatalog.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe VariableWL.NumericProgram
variable {n : ℕ}
structure Listing (n : ℕ) where
  rows : Expr n
  internal : Expr n
  scalars : Expr n
  ands : Expr n
  edges : Expr n
  requests : Expr n
  validScalar : Expr (n+1)
  validAnd : Expr (n+1)
  validEdge : Expr (n+1)
  validRequest : Expr (n+1)
  source : Expr (n+1)
  destination : Expr (n+1)
  destinationForm : Expr (n+1)
  domain : Expr (n+3)
  map : Expr (n+3)
  requestGate : Expr (n+1)
  requestTest : Expr (n+1)
  requestDomain : Expr (n+3)
  marked : Expr n
  epsilon : Expr n
namespace Listing
variable (D : Listing n)
def eval (v : Env n) : Data where
  rows := D.rows.number v
  internal := D.internal.number v
  scalars := D.scalars.number v
  ands := D.ands.number v
  edges := D.edges.number v
  requests := D.requests.number v
  validScalar i := D.validScalar.bit (cons (List.replicate i true) v)
  validAnd i := D.validAnd.bit (cons (List.replicate i true) v)
  validEdge i := D.validEdge.bit (cons (List.replicate i true) v)
  validRequest i := D.validRequest.bit (cons (List.replicate i true) v)
  source i := D.source.number (cons (List.replicate i true) v)
  destination i := D.destination.number (cons (List.replicate i true) v)
  destinationForm i := D.destinationForm.number (cons (List.replicate i true) v)
  domain i j a := D.domain.bit (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))
  map i j a := D.map.number (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))
  requestGate i := D.requestGate.number (cons (List.replicate i true) v)
  requestTest i := D.requestTest.number (cons (List.replicate i true) v)
  requestDomain i j a := D.requestDomain.bit (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))
  marked := D.marked.number v
  epsilon := D.epsilon.number v
def up : Listing (n+1) where
  rows := D.rows.up
  internal := D.internal.up
  scalars := D.scalars.up
  ands := D.ands.up
  edges := D.edges.up
  requests := D.requests.up
  validScalar := underOne D.validScalar
  validAnd := underOne D.validAnd
  validEdge := underOne D.validEdge
  validRequest := underOne D.validRequest
  source := underOne D.source
  destination := underOne D.destination
  destinationForm := underOne D.destinationForm
  domain := underThree D.domain
  map := underThree D.map
  requestGate := underOne D.requestGate
  requestTest := underOne D.requestTest
  requestDomain := underThree D.requestDomain
  marked := D.marked.up
  epsilon := D.epsilon.up
 theorem eval_up (v : Env n) (a : Word) : D.up.eval (cons a v)=D.eval v := by
  dsimp only [eval,up]
  congr 1
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i j a; exact underThree_bit ..
  · funext i j a; exact underThree_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i j a; exact underThree_bit ..
def gates : Expr n := add D.scalars D.ands
def edgeCode (C : Expr n) : Expr n := choose (lt C D.edges) C
  (choose (lt C (mul (numeral 2) D.edges)) (sub C D.edges) (sub C (mul (numeral 2) D.edges)))
noncomputable def affineSource (C : Expr n) : Expr n := choose (lt C (mul (numeral 2) D.edges))
  (applyNat D.source (D.edgeCode C)) (choose (lt C (mul (numeral 3) D.edges))
    (add D.gates (D.edgeCode C)) (applyNat D.requestGate (sub C (mul (numeral 3) D.edges))))
noncomputable def affineTarget (C : Expr n) : Expr n := choose (lt C (mul (numeral 2) D.edges))
  (add D.gates (D.edgeCode C)) (choose (lt C (mul (numeral 3) D.edges))
    (applyNat D.destination (D.edgeCode C)) (add D.gates D.edges))
noncomputable def affineDomain (C I A : Expr n) : Expr n := choose (lt C (mul (numeral 3) D.edges))
  (applyNat₃ D.domain (D.edgeCode C) I A) (applyNat₃ D.requestDomain (sub C (mul (numeral 3) D.edges)) I A)
noncomputable def affineMap (C I A : Expr n) : Expr n := choose
  (conj (le (mul (numeral 2) D.edges) C) (lt C (mul (numeral 3) D.edges)))
    (applyNat₃ D.map (D.edgeCode C) I A) A
noncomputable def affineDimension (P : Expr n) : Expr n := choose (lt P D.scalars) (numeral 1)
  (choose (lt P (add D.gates D.edges)) (numeral 2) (numeral 1))
noncomputable def affineLeft (C : Expr n) : Expr n := choose (lt C (mul (numeral 2) D.edges))
  (choose (lt (applyNat D.source (D.edgeCode C)) D.scalars)
    (numeral (AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0)))
    (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) ((LinearMap.proj (0 : Fin 2) : Affine.Vec 2 →ₗ[Affine.Bit] Affine.Bit)+LinearMap.proj 1))))
  (choose (lt C (mul (numeral 3) D.edges))
    (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) ((LinearMap.proj (0 : Fin 2) : Affine.Vec 2 →ₗ[Affine.Bit] Affine.Bit)+LinearMap.proj 1)))
    (numeral (AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0))))
noncomputable def affineRight (C : Expr n) : Expr n := choose (lt C D.edges)
  (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 0)))
  (choose (lt C (mul (numeral 2) D.edges)) (numeral (AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 1)))
    (choose (lt C (mul (numeral 3) D.edges)) (applyNat D.destinationForm (D.edgeCode C))
      (numeral (AffineAlphabet.encodeForm (by decide : 1≤2) 0))))
noncomputable def affineConstant (C : Expr n) : Expr n := choose (lt C (mul (numeral 3) D.edges))
  (numeral 0) (applyNat D.requestTest (sub C (mul (numeral 3) D.edges)))
noncomputable def affineValidReal (I : Expr n) : Expr n := choose (lt I D.gates)
  (choose (lt I D.scalars) (applyNat D.validScalar I) (applyNat D.validAnd (sub I D.scalars)))
  (choose (lt (sub I D.gates) D.edges) (applyNat D.validEdge (sub I D.gates)) (literal [true]))
noncomputable def affineValidComparison (C : Expr n) : Expr n := choose (lt C (add D.edges (add D.edges D.edges)))
  (choose (lt C D.edges) (applyNat D.validEdge C) (choose (lt (sub C D.edges) D.edges)
    (applyNat D.validEdge (sub C D.edges)) (applyNat D.validEdge (sub (sub C D.edges) D.edges))))
  (applyNat D.validRequest (sub C (add D.edges (add D.edges D.edges))))
 theorem gates_number (v : Env n) : (D.gates).number v=(D.eval v).gates := by
  simp only [gates,add_number,eval,Data.gates]
 theorem edgeCode_number (C : Expr n) (v : Env n) : (D.edgeCode C).number v=(D.eval v).edgeCode (C.number v) := by
  simp only [edgeCode,choose_number,mul_number,sub_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.edgeCode] ; rfl
 theorem affineSource_number (C : Expr n) (v : Env n) : (D.affineSource C).number v=(D.eval v).affine.source (C.number v) := by
  simp only [affineSource,gates_number,edgeCode_number,applyNat_number,choose_number,add_number,mul_number,sub_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineTarget_number (C : Expr n) (v : Env n) : (D.affineTarget C).number v=(D.eval v).affine.target (C.number v) := by
  simp only [affineTarget,gates_number,edgeCode_number,applyNat_number,choose_number,add_number,mul_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineDomain_bit (C I A : Expr n) (v : Env n) : (D.affineDomain C I A).bit v=(D.eval v).affine.domain (C.number v) (I.number v) (A.number v) := by
  simp only [affineDomain,edgeCode_number,applyNat₃_bit,choose_bit,mul_number,sub_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineMap_number (C I A : Expr n) (v : Env n) : (D.affineMap C I A).number v=(D.eval v).affine.map (C.number v) (I.number v) (A.number v) := by
  simp only [affineMap,edgeCode_number,applyNat₃_number,choose_number,mul_number,numeral_number,lt_bit,le_bit,conj_bit,decide_eq_true_eq,Bool.and_eq_true,eval,Data.affine,Data.gates] ; rfl
 theorem affineDimension_number (P : Expr n) (v : Env n) : (D.affineDimension P).number v=(D.eval v).affine.realDimension (P.number v) := by
  simp only [affineDimension,gates_number,choose_number,add_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineLeft_number (C : Expr n) (v : Env n) : (D.affineLeft C).number v=(D.eval v).affine.leftForm (C.number v) := by
  simp only [affineLeft,edgeCode_number,applyNat_number,choose_number,mul_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineRight_number (C : Expr n) (v : Env n) : (D.affineRight C).number v=(D.eval v).affine.rightForm (C.number v) := by
  simp only [affineRight,edgeCode_number,applyNat_number,choose_number,mul_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineConstant_number (C : Expr n) (v : Env n) : (D.affineConstant C).number v=(D.eval v).affine.rightConstant (C.number v) := by
  simp only [affineConstant,applyNat_number,choose_number,mul_number,sub_number,numeral_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
 theorem affineValidReal_bit (I : Expr n) (v : Env n) : (D.affineValidReal I).bit v=(D.eval v).affine.validReal (I.number v) := by
  simp only [affineValidReal,gates_number,applyNat_bit,choose_bit,sub_number,lt_bit,decide_eq_true_eq,BlockCatalog.Program.literal_true_bit,eval,Data.affine,Data.gates] ; rfl
 theorem affineValidComparison_bit (C : Expr n) (v : Env n) : (D.affineValidComparison C).bit v=(D.eval v).affine.validComparison (C.number v) := by
  simp only [affineValidComparison,applyNat_bit,choose_bit,add_number,sub_number,lt_bit,decide_eq_true_eq,eval,Data.affine,Data.gates] ; rfl
noncomputable def affine : AffineCatalog.Program.Listing n where
  rows := D.rows
  internal := D.internal
  reals := add D.gates (add D.edges (numeral 1))
  comparisons := add (add D.edges (add D.edges D.edges)) D.requests
  validReal := D.up.affineValidReal (input 0)
  validComparison := D.up.affineValidComparison (input 0)
  source := D.up.affineSource (input 0)
  target := D.up.affineTarget (input 0)
  domain := D.up.up.up.affineDomain (input 0) (input 1) (input 2)
  map := D.up.up.up.affineMap (input 0) (input 1) (input 2)
  realDimension := D.up.affineDimension (input 0)
  leftForm := D.up.affineLeft (input 0)
  rightForm := D.up.affineRight (input 0)
  leftConstant := numeral 0
  rightConstant := D.up.affineConstant (input 0)
  marked := D.marked
  epsilon := D.epsilon
 theorem affine_base_eval (v : Env n) : (D.affine.eval v).toData=(D.eval v).affine.toData := by
  apply BlockCatalog.Data.ext_fields
  · rfl
  · rfl
  · change (add D.gates (add D.edges (numeral 1))).number v=(D.eval v).gates+((D.eval v).edges+1)
    rw [add_number,gates_number,add_number,numeral_number]; rfl
  · change (add (add D.edges (add D.edges D.edges)) D.requests).number v=_
    simp only [add_number]; rfl
  · funext i
    change (D.up.affineValidReal (input 0)).bit (cons (List.replicate i true) v)=_
    rw [affineValidReal_bit,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i
    change (D.up.affineValidComparison (input 0)).bit (cons (List.replicate i true) v)=_
    rw [affineValidComparison_bit,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i
    change (D.up.affineSource (input 0)).number (cons (List.replicate i true) v)=_
    rw [affineSource_number,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i
    change (D.up.affineTarget (input 0)).number (cons (List.replicate i true) v)=_
    rw [affineTarget_number,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i j a
    change (D.up.up.up.affineDomain (input 0) (input 1) (input 2)).bit
      (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))=_
    rw [affineDomain_bit,eval_up,eval_up,eval_up]; simp only [input_number,cons_zero,cons_one,cons_two,List.length_replicate]
  · funext i j a
    change (D.up.up.up.affineMap (input 0) (input 1) (input 2)).number
      (cons (List.replicate i true) (cons (List.replicate j true) (cons (List.replicate a true) v)))=_
    rw [affineMap_number,eval_up,eval_up,eval_up]; simp only [input_number,cons_zero,cons_one,cons_two,List.length_replicate]
 theorem affine_eval (v : Env n) : D.affine.eval v=(D.eval v).affine := by
  apply AffineCatalog.Data.ext_fields
  · exact D.affine_base_eval v
  · funext i
    change (D.up.affineDimension (input 0)).number (cons (List.replicate i true) v)=_
    rw [affineDimension_number,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i
    change (D.up.affineLeft (input 0)).number (cons (List.replicate i true) v)=_
    rw [affineLeft_number,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i
    change (D.up.affineRight (input 0)).number (cons (List.replicate i true) v)=_
    rw [affineRight_number,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · funext i; rfl
  · funext i
    change (D.up.affineConstant (input 0)).number (cons (List.replicate i true) v)=_
    rw [affineConstant_number,eval_up]; simp only [input_number,cons_zero,List.length_replicate]
  · rfl
  · rfl
end Listing
end VariableWL.CircuitCatalog.Program

namespace VariableWL.Binary
 theorem number_bit {d : ℕ} (x : Digits d) : ∀i : Fin d,(number x).testBit i.val=x i := by
  induction d with
  | zero => intro i; exact Fin.elim0 i
  | succ d ih =>
    intro i
    have he : number x=Nat.bit (x 0) (number (fun j : Fin d=>x j.succ)) := by
      cases hb : x 0 <;> simp [number,hb,Nat.bit,Nat.add_comm]
    rw [he]
    refine Fin.cases ?_ (fun j=>?_) i
    · cases hb : x 0 <;> simp [Nat.bit,Nat.testBit_eq_decide_div_mod_eq]
    · rw [Fin.val_succ,Nat.testBit_bit_succ]
      exact ih (fun j : Fin d=>x j.succ) j
end VariableWL.Binary
namespace VariableWL.Circuit.ProductCellular.Data
 theorem threshold_bit {L : Type uVariable1} {d m : ℕ} (D : Data L d m) (i : Fin d) : m.testBit i.val=D.threshold i := by
  simpa only [D.number_threshold] using (Binary.number_bit D.threshold i)
 theorem input_bit {L : Type uVariable2} {d m : ℕ} (D : Data L d m) (j : Fin m) (i : Fin d) : j.val.testBit i.val=D.inputBits j i := by
  simpa only [D.number_inputBits] using (Binary.number_bit (D.inputBits j) i)
end VariableWL.Circuit.ProductCellular.Data
namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
 theorem binaryDigit_total {n : ℕ} (N I : Expr n) (v : Env n) :
    (binaryDigit N I).bit v=(N.number v).testBit (I.number v) := by
  by_cases h : I.number v<(N.number v).size
  · exact binaryDigit_bit N I v h
  · have hp : N.number v<2^I.number v := by
      have := Nat.lt_size (n := N.number v) (m := I.number v)
      omega
    rw [Nat.testBit_eq_false_of_lt hp,binaryDigit,eq_bit,mod_number,div_number,capPow_number,add_number]
    simp only [numeral_number,Nat.min_eq_right (show N.number v+1≤2^I.number v by omega),
      Nat.div_eq_of_lt (Nat.lt_succ_self _),Nat.zero_mod]
    rfl
end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.CellularCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
variable {L : Type uVariable3} {d m : ℕ} (P : Presentation L)
noncomputable def triple : Presentation (Cellular.Triple L) := P.product (P.product P)
noncomputable def ands : Presentation (Cellular.Triple L × Bool) := (triple P).product Presentation.boolean
noncomputable def kind (d : ℕ) : Presentation (ProductCellular.Kind d) :=
  ((Presentation.fin d).product (Presentation.fin d).option).sum
    ((Presentation.fin d).sum (((Presentation.fin d).product (Presentation.fin d).option).sum Presentation.boolean))
noncomputable def edge : Presentation (ProductCellular.Edge L d) := (triple P).product (kind d)
noncomputable def zeroBit (D : ProductCellular.Data L d m) : Presentation {h : Fin d // D.threshold h=false} :=
  (Presentation.fin d).filter (fun i=>!(m.testBit i)) (fun h=>D.threshold h=false)
    (by intro i; simp only [Presentation.fin_encode,←D.threshold_bit i,Bool.not_eq_true'])
noncomputable def accepting (D : ProductCellular.Data L d m) : Presentation {f : L // f∈D.accepting} :=
  P.filter (fun i=>decide (∃f,P.encode f=i ∧ f∈D.accepting)) (fun f=>f∈D.accepting)
    (by intro f; simp only [decide_eq_true_eq,P.encode_injective.eq_iff]; simp)
noncomputable def request (D : ProductCellular.Data L d m) : Presentation D.Request :=
  ((Presentation.fin m).sum (zeroBit D).option).sum (accepting P D)
structure Data where
  bits : ℕ
  inputLength : ℕ
  letters : ℕ
  internal : ℕ
  rule : ℕ → ℕ → ℕ → ℕ
  input : ℕ → ℕ
  blank : ℕ
  accepting : ℕ → Bool
  marked : ℕ
  epsilon : ℕ
namespace Data
variable (D : Data)
def leftEnd : ℕ := D.bits*(1+D.bits)
def centerEnd : ℕ := D.leftEnd+D.bits
def rightEnd : ℕ := D.centerEnd+D.leftEnd
def kinds : ℕ := D.rightEnd+2
def triples : ℕ := D.letters*(D.letters*D.letters)
def tripleCode (e : ℕ) : ℕ := e/D.kinds
def kindCode (e : ℕ) : ℕ := e%D.kinds
def first (t : ℕ) : ℕ := t/(D.letters*D.letters)
def second (t : ℕ) : ℕ := (t/D.letters)%D.letters
def third (t : ℕ) : ℕ := t%D.letters
def kindTime (k : ℕ) : ℕ := if k<D.leftEnd then k/(1+D.bits) else
  if k<D.centerEnd then k-D.leftEnd else (k-D.centerEnd)/(1+D.bits)
def kindPosition (k : ℕ) : ℕ := if k<D.leftEnd then k%(1+D.bits) else (k-D.centerEnd)%(1+D.bits)
def source (e : ℕ) : ℕ := let k:=D.kindCode e; let t:=D.tripleCode e
  if k<D.leftEnd then D.first t else if k<D.centerEnd then D.second t else
    if k<D.rightEnd then D.third t else D.letters+(t*2+(k-D.rightEnd))
def destination (e : ℕ) : ℕ := let k:=D.kindCode e; let t:=D.tripleCode e
  if k<D.centerEnd then D.letters+t*2 else if k<D.rightEnd+1 then D.letters+(t*2+1)
    else D.rule (D.first t) (D.second t) (D.third t)
noncomputable def destinationForm (e : ℕ) : ℕ := let k:=D.kindCode e
  if k<D.leftEnd then AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 0)
    else if k<D.rightEnd then AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 1)
    else if k<D.rightEnd+1 then AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 0)
    else AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0)
def carryDomain (bit : ℕ) (h i a : ℕ) : Bool := if i<h then decide (a=bit) else if i=h then decide (a=1-bit) else true
def cyclicDomain (bit : ℕ) (h i a : ℕ) : Bool := if h=0 then decide (a=bit) else carryDomain bit (h-1) i a
def domain (e i a : ℕ) : Bool := let k:=D.kindCode e
  if k<D.rightEnd then if i<D.bits then carryDomain 1 (D.kindTime k) i a
    else if k<D.leftEnd then cyclicDomain 1 (D.kindPosition k) (i-D.bits) a
    else if k<D.centerEnd then true else cyclicDomain 0 (D.kindPosition k) (i-D.bits) a
  else true
def map (e i a : ℕ) : ℕ := let k:=D.kindCode e
  if k<D.rightEnd then if i<D.bits then (if i≤D.kindTime k then 1-a else a)
    else if k<D.leftEnd ∨ D.centerEnd≤k then
      (if D.kindPosition k=0 ∨ i-D.bits<D.kindPosition k then 1-a else a) else a
  else a
def initialEnd : ℕ := D.inputLength+(1+D.bits)
def validRequest (b : ℕ) : Bool := if b<D.inputLength then true else if b=D.inputLength then true
  else if b<D.initialEnd then !(D.inputLength.testBit (b-D.inputLength-1)) else D.accepting (b-D.initialEnd)
def requestGate (b : ℕ) : ℕ := if b<D.inputLength then D.input b else if b<D.initialEnd then D.blank else b-D.initialEnd
def requestTest (b : ℕ) : ℕ := if b<D.initialEnd then 0 else 1
def requestPositionDomain (b i a : ℕ) : Bool := if b<D.inputLength then decide (a=(b.testBit i).toNat)
  else if b<D.initialEnd then
    (if b=D.inputLength ∨ b - D.inputLength - 1 < i then decide (a=(D.inputLength.testBit i).toNat)
      else if i=b-D.inputLength-1 then decide (a=1) else true) else true
def requestDomain (b i a : ℕ) : Bool := if i<D.bits then decide (a=D.requestTest b)
  else D.requestPositionDomain b (i-D.bits) a
noncomputable def catalog : CircuitCatalog.Data where
  rows := D.bits+D.bits
  internal := D.internal
  scalars := D.letters
  ands := D.triples*2
  edges := D.triples*D.kinds
  requests := D.initialEnd+D.letters
  validScalar _ := true
  validAnd _ := true
  validEdge _ := true
  validRequest := D.validRequest
  source := D.source
  destination := D.destination
  destinationForm := D.destinationForm
  domain := D.domain
  map := D.map
  requestGate := D.requestGate
  requestTest := D.requestTest
  requestDomain := D.requestDomain
  marked := D.marked
  epsilon := D.epsilon
end Data
end VariableWL.CellularCatalog

namespace VariableWL.Descriptor.Presentation
variable {A : Type uVariable4} {B : Type uVariable5}
@[simp] theorem product_bound (P : Presentation A) (Q : Presentation B) : (P.product Q).bound=P.bound*Q.bound := rfl
@[simp] theorem product_valid (P : Presentation A) (Q : Presentation B) (i : ℕ) : (P.product Q).valid i=(P.valid (i/Q.bound) && Q.valid (i%Q.bound)) := rfl
@[simp] theorem sum_valid (P : Presentation A) (Q : Presentation B) (i : ℕ) : (P.sum Q).valid i=(if i<P.bound then P.valid i else Q.valid (i-P.bound)) := rfl
@[simp] theorem filter_bound (P : Presentation A) (Q : ℕ → Bool) (T : A → Prop) (h) : (P.filter Q T h).bound=P.bound := rfl
@[simp] theorem filter_valid (P : Presentation A) (Q : ℕ → Bool) (T : A → Prop) (h) (i : ℕ) : (P.filter Q T h).valid i=(P.valid i && Q i) := rfl
@[simp] theorem option_bound (P : Presentation A) : P.option.bound=1+P.bound := rfl
@[simp] theorem option_valid (P : Presentation A) (i : ℕ) : P.option.valid i=(if i<1 then true else P.valid (i-1)) := rfl
@[simp] theorem fin_bound (d : ℕ) : (fin d).bound=d := rfl
@[simp] theorem fin_valid (d i : ℕ) : (fin d).valid i=true := rfl
end VariableWL.Descriptor.Presentation

end OAI
