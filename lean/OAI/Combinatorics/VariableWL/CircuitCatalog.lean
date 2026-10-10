import OAI.Combinatorics.VariableWL.AffineCatalog

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10 uVariable11

namespace VariableWL.AffineCatalog.Program
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
open VariableWL.NumericProgram
variable {n : ℕ}
structure Listing (n : ℕ) extends BlockCatalog.Program.Listing n where
  realDimension : Expr (n+1)
  leftForm : Expr (n+1)
  rightForm : Expr (n+1)
  leftConstant : Expr (n+1)
  rightConstant : Expr (n+1)
  marked : Expr n
  epsilon : Expr n
namespace Listing
variable (D : Listing n)
def eval (v : Env n) : Data where
  toData := D.toListing.eval v
  realDimension i := D.realDimension.number (cons (List.replicate i true) v)
  leftForm i := D.leftForm.number (cons (List.replicate i true) v)
  rightForm i := D.rightForm.number (cons (List.replicate i true) v)
  leftConstant i := D.leftConstant.number (cons (List.replicate i true) v)
  rightConstant i := D.rightConstant.number (cons (List.replicate i true) v)
  marked := D.marked.number v
  epsilon := D.epsilon.number v
def up : Listing (n+1) where
  toListing := D.toListing.up
  realDimension := underOne D.realDimension
  leftForm := underOne D.leftForm
  rightForm := underOne D.rightForm
  leftConstant := underOne D.leftConstant
  rightConstant := underOne D.rightConstant
  marked := D.marked.up
  epsilon := D.epsilon.up
 theorem eval_up (v : Env n) (a : Word) : D.up.eval (cons a v)=D.eval v := by
  dsimp only [eval,up]
  congr 1
  · exact D.toListing.eval_up v a
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
def vertexDimension (T : Expr n) : Expr n := choose (lt T D.reals) (applyNat D.realDimension T) (numeral 1)
def horizontalDimension (H : Expr n) : Expr n := D.vertexDimension (D.toListing.htype H)
def squareLeftDimension (S : Expr n) : Expr n := D.vertexDimension (D.toListing.left (D.toListing.slink S))
def squareRightDimension (S : Expr n) : Expr n := D.vertexDimension (D.toListing.right (D.toListing.slink S))
def dimension (B : Expr n) : Expr n := choose (lt B D.toListing.horizontals) (D.horizontalDimension B)
  (add (add (D.squareLeftDimension (sub B D.toListing.horizontals)) (D.squareRightDimension (sub B D.toListing.horizontals))) (numeral 2))
def readDimension (A : Expr n) : Expr n := choose (lt A D.toListing.horizontals) (D.horizontalDimension A) (numeral 1)
noncomputable def linkLeft (L : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) (numeral 0))
  (applyNat D.leftForm (div L (add D.internal (numeral 1))))
  (numeral (AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj (0 : Fin 1))))
noncomputable def linkRight (L : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) D.internal)
  (applyNat D.rightForm (div L (add D.internal (numeral 1))))
  (numeral (AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj (0 : Fin 1))))
def linkLeftConstant (L : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) (numeral 0))
  (applyNat D.leftConstant (div L (add D.internal (numeral 1)))) (numeral 0)
def linkRightConstant (L : Expr n) : Expr n := choose (eq (mod L (add D.internal (numeral 1))) D.internal)
  (applyNat D.rightConstant (div L (add D.internal (numeral 1)))) (numeral 0)
def constant (S : Expr n) : Expr n := mod (mul D.epsilon (choose (eq (D.toListing.srow S) D.marked)
  (add (D.linkLeftConstant (D.toListing.slink S)) (D.linkRightConstant (D.toListing.slink S))) (numeral 0))) (numeral 2)
noncomputable def zeroOrder (B : Expr n) : Expr n := AffineAlphabet.Program.zeroOrder (D.dimension B)
noncomputable def readOrder (B A : Expr n) : Expr n := choose (lt B D.toListing.horizontals)
  (AffineAlphabet.Program.horizontalOrder (D.horizontalDimension B))
  (AffineAlphabet.Program.squareOrder (D.squareLeftDimension (sub B D.toListing.horizontals))
    (D.squareRightDimension (sub B D.toListing.horizontals))
    (choose (eq A (D.toListing.squareLeft (sub B D.toListing.horizontals))) (numeral 0)
      (choose (eq A (D.toListing.squareRight (sub B D.toListing.horizontals))) (numeral 1)
        (choose (eq A (D.toListing.squareBottom (sub B D.toListing.horizontals))) (numeral 2) (numeral 3)))))
noncomputable def legal (B I : Expr n) : Expr n := choose (lt B D.toListing.horizontals)
  (AffineAlphabet.Program.horizontalLegal (D.horizontalDimension B) I)
  (AffineAlphabet.Program.squareLegal (D.linkLeft (D.toListing.slink (sub B D.toListing.horizontals)))
    (D.linkRight (D.toListing.slink (sub B D.toListing.horizontals))) (D.constant (sub B D.toListing.horizontals)) I)
 theorem vertexDimension_number (T : Expr n) (v : Env n) : (D.vertexDimension T).number v=(D.eval v).vertexDimension (T.number v) := by
  simp only [vertexDimension,lt_bit,applyNat_number,choose_number,numeral_number,lt_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.vertexDimension,eval] ; rfl

 theorem horizontalDimension_number (H : Expr n) (v : Env n) : (D.horizontalDimension H).number v=(D.eval v).horizontalDimension (H.number v) := by
  simp only [horizontalDimension,vertexDimension_number,BlockCatalog.Program.Listing.htype_number,BlockCatalog.Program.Listing.eval,Data.horizontalDimension,eval]

 theorem squareLeftDimension_number (S : Expr n) (v : Env n) : (D.squareLeftDimension S).number v=(D.eval v).squareLeftDimension (S.number v) := by
  simp only [squareLeftDimension,vertexDimension_number,BlockCatalog.Program.Listing.left_number,BlockCatalog.Program.Listing.slink_number,BlockCatalog.Program.Listing.eval,Data.squareLeftDimension,eval]

 theorem squareRightDimension_number (S : Expr n) (v : Env n) : (D.squareRightDimension S).number v=(D.eval v).squareRightDimension (S.number v) := by
  simp only [squareRightDimension,vertexDimension_number,BlockCatalog.Program.Listing.right_number,BlockCatalog.Program.Listing.slink_number,BlockCatalog.Program.Listing.eval,Data.squareRightDimension,eval]

 theorem dimension_number (B : Expr n) (v : Env n) : (D.dimension B).number v=(D.eval v).dimension (B.number v) := by
  simp only [dimension,horizontalDimension_number,squareLeftDimension_number,squareRightDimension_number,BlockCatalog.Program.Listing.horizontals_number,choose_number,add_number,sub_number,numeral_number,lt_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.dimension,eval] ; rfl

 theorem readDimension_number (A : Expr n) (v : Env n) : (D.readDimension A).number v=(D.eval v).readDimension (A.number v) := by
  simp only [readDimension,horizontalDimension_number,BlockCatalog.Program.Listing.horizontals_number,choose_number,numeral_number,lt_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.readDimension,eval] ; rfl

 theorem linkLeft_number (L : Expr n) (v : Env n) : (D.linkLeft L).number v=(D.eval v).linkLeft (L.number v) := by
  simp only [linkLeft,applyNat_number,choose_number,add_number,div_number,mod_number,numeral_number,eq_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.linkLeft,eval] ; rfl

 theorem linkRight_number (L : Expr n) (v : Env n) : (D.linkRight L).number v=(D.eval v).linkRight (L.number v) := by
  simp only [linkRight,applyNat_number,choose_number,add_number,div_number,mod_number,numeral_number,eq_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.linkRight,eval] ; rfl

 theorem linkLeftConstant_number (L : Expr n) (v : Env n) : (D.linkLeftConstant L).number v=(D.eval v).linkLeftConstant (L.number v) := by
  simp only [linkLeftConstant,applyNat_number,choose_number,add_number,div_number,mod_number,numeral_number,eq_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.linkLeftConstant,eval] ; rfl

 theorem linkRightConstant_number (L : Expr n) (v : Env n) : (D.linkRightConstant L).number v=(D.eval v).linkRightConstant (L.number v) := by
  simp only [linkRightConstant,applyNat_number,choose_number,add_number,div_number,mod_number,numeral_number,eq_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.linkRightConstant,eval] ; rfl

 theorem constant_number (S : Expr n) (v : Env n) : (D.constant S).number v=(D.eval v).constant (S.number v) := by
  simp only [constant,linkLeftConstant_number,linkRightConstant_number,BlockCatalog.Program.Listing.srow_number,BlockCatalog.Program.Listing.slink_number,choose_number,add_number,mul_number,mod_number,numeral_number,eq_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.constant,eval] ; rfl

 theorem zeroOrder_number (B : Expr n) (v : Env n) : (D.zeroOrder B).number v=(D.eval v).zeroOrder (B.number v) := by
  simp only [zeroOrder,AffineAlphabet.Program.zeroOrder_number,dimension_number,BlockCatalog.Program.Listing.eval,Data.zeroOrder,eval]

 theorem readOrder_number (B A : Expr n) (v : Env n) : (D.readOrder B A).number v=(D.eval v).readOrder (B.number v) (A.number v) := by
  simp only [readOrder,AffineAlphabet.Program.horizontalOrder_number,AffineAlphabet.Program.squareOrder_number,horizontalDimension_number,squareLeftDimension_number,squareRightDimension_number,BlockCatalog.Program.Listing.horizontals_number,BlockCatalog.Program.Listing.squareLeft_number,BlockCatalog.Program.Listing.squareRight_number,BlockCatalog.Program.Listing.squareBottom_number,choose_number,sub_number,numeral_number,eq_bit,lt_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.readOrder,eval] ; rfl

 theorem legal_bit (B I : Expr n) (v : Env n) : (D.legal B I).bit v=(D.eval v).legal (B.number v) (I.number v) := by
  simp only [legal,AffineAlphabet.Program.horizontalLegal_bit,AffineAlphabet.Program.squareLegal_bit,horizontalDimension_number,linkLeft_number,linkRight_number,constant_number,BlockCatalog.Program.Listing.horizontals_number,BlockCatalog.Program.Listing.slink_number,choose_bit,sub_number,lt_bit,decide_eq_true_eq,BlockCatalog.Program.Listing.eval,Data.legal,eval] ; rfl

noncomputable def core : BlockDescriptor.Program.Listing n where
  blocks := D.toListing.blocks
  validBlock := D.toListing.up.validBlock (input 0)
  reads := D.toListing.reads
  validRead := D.toListing.up.readValid (input 0)
  has := D.toListing.up.up.has (input 0) (input 1)
  dimension := D.up.dimension (input 0)
  readDimension := D.up.readDimension (input 0)
  zeroOrder := D.up.zeroOrder (input 0)
  readOrder := D.up.up.readOrder (input 0) (input 1)
  legal := D.up.up.legal (input 0) (input 1)
 theorem core_blocks_field : D.core.blocks=D.toListing.blocks := rfl
 theorem core_blocks_eval (v : Env n) : (D.core.eval v).blocks=(D.eval v).core.blocks := by
  rw [BlockDescriptor.Program.Listing.eval_blocks,core_blocks_field,Data.core_blocks_eq]
  change D.toListing.blocks.number v=(D.toListing.eval v).blocks
  exact D.toListing.blocks_number v
 theorem core_validBlock_field : D.core.validBlock=D.toListing.up.validBlock (input 0) := rfl
 theorem core_validBlock_eval (v : Env n) : (D.core.eval v).validBlock=(D.eval v).core.validBlock := by
  rw [BlockDescriptor.Program.Listing.eval_validBlock,D.core_validBlock_field,Data.core_validBlock_eq]
  funext i
  rw [BlockCatalog.Program.Listing.validBlock_bit,BlockCatalog.Program.Listing.eval_up,input_number,cons_zero,List.length_replicate]
  rfl
 theorem core_reads_field : D.core.reads=D.toListing.reads := rfl
 theorem core_reads_eval (v : Env n) : (D.core.eval v).reads=(D.eval v).core.reads := by
  rw [BlockDescriptor.Program.Listing.eval_reads,core_reads_field,Data.core_reads_eq]
  change D.toListing.reads.number v=(D.toListing.eval v).reads
  exact D.toListing.reads_number v
 theorem core_validRead_field : D.core.validRead=D.toListing.up.readValid (input 0) := rfl
 theorem core_validRead_eval (v : Env n) : (D.core.eval v).validRead=(D.eval v).core.validRead := by
  rw [BlockDescriptor.Program.Listing.eval_validRead,D.core_validRead_field,Data.core_validRead_eq]
  funext i
  rw [BlockCatalog.Program.Listing.readValid_bit,BlockCatalog.Program.Listing.eval_up,input_number,cons_zero,List.length_replicate]
  rfl
 theorem core_has_eval (v : Env n) : (D.core.eval v).has=(D.eval v).core.has := by
  funext i j
  change (D.toListing.up.up.has (input 0) (input 1)).bit (cons (List.replicate i true) (cons (List.replicate j true) v))=(D.eval v).has i j
  rw [BlockCatalog.Program.Listing.has_bit,BlockCatalog.Program.Listing.eval_up,BlockCatalog.Program.Listing.eval_up]
  simp only [input_number,cons_zero,cons_one,List.length_replicate]
  rfl
 theorem core_dimension_eval (v : Env n) : (D.core.eval v).dimension=(D.eval v).core.dimension := by
  funext i
  change (D.up.dimension (input 0)).number (cons (List.replicate i true) v)=(D.eval v).dimension i
  rw [dimension_number,eval_up,input_number,cons_zero,List.length_replicate]
 theorem core_readDimension_eval (v : Env n) : (D.core.eval v).readDimension=(D.eval v).core.readDimension := by
  funext i
  change (D.up.readDimension (input 0)).number (cons (List.replicate i true) v)=(D.eval v).readDimension i
  rw [readDimension_number,eval_up,input_number,cons_zero,List.length_replicate]
 theorem core_zeroOrder_eval (v : Env n) : (D.core.eval v).zeroOrder=(D.eval v).core.zeroOrder := by
  funext i
  change (D.up.zeroOrder (input 0)).number (cons (List.replicate i true) v)=(D.eval v).zeroOrder i
  rw [zeroOrder_number,eval_up,input_number,cons_zero,List.length_replicate]
 theorem core_readOrder_eval (v : Env n) : (D.core.eval v).readOrder=(D.eval v).core.readOrder := by
  funext i j
  change (D.up.up.readOrder (input 0) (input 1)).number (cons (List.replicate i true) (cons (List.replicate j true) v))=(D.eval v).readOrder i j
  rw [readOrder_number,eval_up,eval_up]
  simp only [input_number,cons_zero,cons_one,List.length_replicate]
 theorem core_legal_eval (v : Env n) : (D.core.eval v).legal=(D.eval v).core.legal := by
  funext i j
  change (D.up.up.legal (input 0) (input 1)).bit (cons (List.replicate i true) (cons (List.replicate j true) v))=(D.eval v).legal i j
  rw [legal_bit,eval_up,eval_up]
  simp only [input_number,cons_zero,cons_one,List.length_replicate]
 theorem core_eval (v : Env n) : D.core.eval v=(D.eval v).core := by
  exact BlockDescriptor.Core.ext_fields (D.core_blocks_eval v) (D.core_validBlock_eval v) (D.core_reads_eval v) (D.core_validRead_eval v) (D.core_has_eval v) (D.core_dimension_eval v) (D.core_readDimension_eval v) (D.core_zeroOrder_eval v) (D.core_readOrder_eval v) (D.core_legal_eval v)

end Listing
end VariableWL.AffineCatalog.Program

namespace VariableWL.Descriptor.Presentation
attribute [local instance] Classical.propDecidable
@[simp] theorem sum_bound {A : Type uVariable1} {B : Type uVariable2} (P : Presentation A) (Q : Presentation B) : (P.sum Q).bound=P.bound+Q.bound := rfl
noncomputable def unit : Presentation Unit := ofEncoding 1 (fun _=>true) (fun _=>0)
  (by intro; decide) (by intro; rfl) (by intro a b _; exact Subsingleton.elim a b)
  (by intro i hi _; exact ⟨(),by omega⟩)
@[simp] theorem unit_encode (u : Unit) : unit.encode u=0 := rfl
noncomputable def fixed (A : Type uVariable3) [Fintype A] : Presentation A :=
  ofEncoding (Fintype.card A) (fun _=>true) (fun a=>(Fintype.equivFin A a).val)
    (fun a=>(Fintype.equivFin A a).isLt) (fun _=>rfl)
    (fun _ _ h=>(Fintype.equivFin A).injective (Fin.ext h))
    (fun i hi _=>⟨(Fintype.equivFin A).symm ⟨i,hi⟩,by simp only [Equiv.apply_symm_apply]⟩)
def optionEquiv (A : Type uVariable4) : Unit ⊕ A ≃ Option A where
  toFun := Sum.elim (fun _=>none) some
  invFun := Option.elim' (.inl ()) Sum.inr
  left_inv a := by rcases a with u|a; cases u; rfl; rfl
  right_inv a := by cases a <;> rfl
noncomputable def option {A : Type uVariable5} (P : Presentation A) : Presentation (Option A) :=
  (unit.sum P).transport (optionEquiv A)
@[simp] theorem option_none {A : Type uVariable6} (P : Presentation A) : P.option.encode none=0 := rfl
@[simp] theorem option_some {A : Type uVariable7} (P : Presentation A) (a : A) : P.option.encode (some a)=1+P.encode a := rfl
end VariableWL.Descriptor.Presentation

namespace VariableWL.CircuitCatalog
open Descriptor Circuit VariableWL.Affine
attribute [local instance] Classical.propDecidable
structure Data where
  rows : ℕ
  internal : ℕ
  scalars : ℕ
  ands : ℕ
  edges : ℕ
  requests : ℕ
  validScalar : ℕ → Bool
  validAnd : ℕ → Bool
  validEdge : ℕ → Bool
  validRequest : ℕ → Bool
  source : ℕ → ℕ
  destination : ℕ → ℕ
  destinationForm : ℕ → ℕ
  domain : ℕ → ℕ → ℕ → Bool
  map : ℕ → ℕ → ℕ → ℕ
  requestGate : ℕ → ℕ
  requestTest : ℕ → ℕ
  requestDomain : ℕ → ℕ → ℕ → Bool
  marked : ℕ
  epsilon : ℕ
namespace Data
variable (D : Data)
def gates : ℕ := D.scalars+D.ands
def edgeCode (c : ℕ) : ℕ := if c<D.edges then c else if c<2*D.edges then c-D.edges else c-2*D.edges
noncomputable def affine : AffineCatalog.Data where
  rows := D.rows
  internal := D.internal
  reals := D.gates+(D.edges+1)
  comparisons := D.edges+(D.edges+D.edges)+D.requests
  validReal i := if i<D.gates then (if i<D.scalars then D.validScalar i else D.validAnd (i-D.scalars))
    else if i-D.gates<D.edges then D.validEdge (i-D.gates) else true
  validComparison c := if c<D.edges+(D.edges+D.edges) then
    (if c<D.edges then D.validEdge c else if c-D.edges<D.edges then D.validEdge (c-D.edges)
      else D.validEdge (c-D.edges-D.edges)) else D.validRequest (c-(D.edges+(D.edges+D.edges)))
  source c := if c<2*D.edges then D.source (D.edgeCode c) else
    if c<3*D.edges then D.gates+D.edgeCode c else D.requestGate (c-3*D.edges)
  target c := if c<2*D.edges then D.gates+D.edgeCode c else
    if c<3*D.edges then D.destination (D.edgeCode c) else D.gates+D.edges
  domain c i a := if c<3*D.edges then D.domain (D.edgeCode c) i a else D.requestDomain (c-3*D.edges) i a
  map c i a := if 2*D.edges≤c ∧ c<3*D.edges then D.map (D.edgeCode c) i a else a
  realDimension p := if p<D.scalars then 1 else if p<D.gates+D.edges then 2 else 1
  leftForm c := if c<2*D.edges then
    (if D.source (D.edgeCode c)<D.scalars then AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0)
      else AffineAlphabet.encodeForm (by decide : 2≤2) ((LinearMap.proj (0 : Fin 2) : Vec 2 →ₗ[Bit] Bit)+LinearMap.proj 1))
    else if c<3*D.edges then AffineAlphabet.encodeForm (by decide : 2≤2)
      ((LinearMap.proj (0 : Fin 2) : Vec 2 →ₗ[Bit] Bit)+LinearMap.proj 1)
    else AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0)
  rightForm c := if c<D.edges then AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 0)
    else if c<2*D.edges then AffineAlphabet.encodeForm (by decide : 2≤2) (LinearMap.proj 1)
    else if c<3*D.edges then D.destinationForm (D.edgeCode c)
    else AffineAlphabet.encodeForm (by decide : 1≤2) 0
  leftConstant _ := 0
  rightConstant c := if c<3*D.edges then 0 else D.requestTest (c-3*D.edges)
  marked := D.marked
  epsilon := D.epsilon
end Data
variable {r n : ℕ} {S : Type uVariable8} {A : Type uVariable9} {E : Type uVariable10} {R : Type uVariable11}
variable (PS : Presentation S) (PA : Presentation A) (PE : Presentation E) (PR : Presentation R)
noncomputable def real : Presentation (Description.Real (S := S) (A := A) (E := E)) :=
  (PS.sum PA).sum (PE.sum Presentation.unit)
noncomputable def comparison : Presentation (Description.Comparison (E := E) (R := R)) :=
  (PE.sum (PE.sum PE)).sum PR
structure Good (C : Description r S A E R) (marked : Fin r) (ε : Bit) (D : Data) : Prop where
  rows : D.rows=r
  internal : D.internal=n
  scalars : D.scalars=PS.bound
  ands : D.ands=PA.bound
  edges : D.edges=PE.bound
  requests : D.requests=PR.bound
  validScalar : D.validScalar=PS.valid
  validAnd : D.validAnd=PA.valid
  validEdge : D.validEdge=PE.valid
  validRequest : D.validRequest=PR.valid
  source : ∀e,D.source (PE.encode e)=(PS.sum PA).encode (C.source e)
  destination : ∀e,D.destination (PE.encode e)=(PS.sum PA).encode (target S A (C.destination e))
  destinationForm : ∀e,D.destinationForm (PE.encode e)=AffineAlphabet.encodeForm
    (by cases C.destination e <;> simp only [dimension] <;> decide) (inputLinear (C.destination e))
  domain : ∀e i a,D.domain (PE.encode e) i.val a.toNat=true ↔ a ∈ C.domain e i
  map : ∀e i a,D.map (PE.encode e) i.val a.toNat=(C.map e i a).toNat
  requestGate : ∀b,D.requestGate (PR.encode b)=PS.encode (C.requestGate b)
  requestTest : ∀b,D.requestTest (PR.encode b)=(if C.requestTest b then 1 else 0)
  requestDomain : ∀b i a,D.requestDomain (PR.encode b) i.val a.toNat=true ↔ a ∈ C.requestDomain b i
  marked : D.marked=marked.val
  epsilon : D.epsilon=ε.val
variable (C : Description r S A E R) (marked : Fin r) (ε : Bit) {D : Data}
variable (h : Good (n := n) PS PA PE PR C marked ε D)
include h
 theorem edge_first (e : E) : D.edgeCode (PE.encode e)=PE.encode e := by
  rw [Data.edgeCode,ite_eq_left (by rw [h.edges]; exact PE.encode_lt e)]
 theorem edge_second (e : E) : D.edgeCode (PE.bound+PE.encode e)=PE.encode e := by
  have he:=PE.encode_lt e
  simp only [Data.edgeCode,h.edges,ite_eq_right (by omega : ¬PE.bound+PE.encode e<PE.bound),
    ite_eq_left (by omega : PE.bound+PE.encode e<2*PE.bound),Nat.add_sub_cancel_left]
 theorem edge_third (e : E) : D.edgeCode (PE.bound+(PE.bound+PE.encode e))=PE.encode e := by
  have he:=PE.encode_lt e
  simp only [Data.edgeCode,h.edges,ite_eq_right (by omega : ¬PE.bound+(PE.bound+PE.encode e)<PE.bound),
    ite_eq_right (by omega : ¬PE.bound+(PE.bound+PE.encode e)<2*PE.bound)]
  omega
 theorem output_form (e : E) : (if D.source (PE.encode e)<D.scalars then
    AffineAlphabet.encodeForm (by decide : 1≤2) (LinearMap.proj 0) else AffineAlphabet.encodeForm (by decide : 2≤2)
      ((LinearMap.proj (0 : Fin 2) : Vec 2 →ₗ[Bit] Bit)+LinearMap.proj 1))=
      AffineAlphabet.encodeForm (RealizationSize.dimension_le_two C.consistency (n := n) (.inl (.inl (C.source e)))) (outputLinear (C.source e)) := by
  rw [h.source,h.scalars]
  cases hg : C.source e with
  | inl s => rw [Presentation.sum_inl,ite_eq_left (PS.encode_lt s)]; rfl
  | inr a => rw [Presentation.sum_inr,ite_eq_right (by omega)]; rfl
 theorem affine_good : AffineCatalog.Good (n := n) (real PS PA PE) (comparison PE PR) C.consistency marked ε D.affine := by
  refine ⟨?_,?_,?_,?_,?_,?_,h.marked,h.epsilon⟩
  · refine ⟨h.rows,h.internal,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp only [Data.affine,Data.gates,h.scalars,h.ands,h.edges,real]; rfl
    · simp only [Data.affine,h.edges,h.requests,comparison]; rfl
    · funext i
      simp only [Data.affine,Data.gates,h.scalars,h.ands,h.edges,h.validScalar,h.validAnd,h.validEdge,real]
      rfl
    · funext i
      simp only [Data.affine,h.edges,h.validEdge,h.validRequest,comparison]
      rfl
    · intro c
      rcases c with (e|(e|e))|b
      all_goals simp only [comparison,real,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,
        Presentation.sum_bound,Data.affine,Data.gates,h.scalars,h.ands,h.edges,
        Circuit.Description.comparisonSource]
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_first PS PA PE PR C marked ε h,h.source] }
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_second PS PA PE PR C marked ε h,h.source] }
      all_goals try { rw [ite_eq_right (by have:=PE.encode_lt e; omega),ite_eq_left (by have:=PE.encode_lt e; omega),edge_third PS PA PE PR C marked ε h] }
      all_goals try { rw [ite_eq_right (by omega),ite_eq_right (by omega)]; have hb : PE.bound+(PE.bound+PE.bound)+PR.encode b-3*PE.bound=PR.encode b := by omega
                      rw [hb,h.requestGate] }
    · intro c
      rcases c with (e|(e|e))|b
      all_goals simp only [comparison,real,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,Presentation.unit_encode,
        Data.affine,Data.gates,h.scalars,h.ands,h.edges,Circuit.Description.comparisonTarget]
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_first PS PA PE PR C marked ε h] }
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_second PS PA PE PR C marked ε h] }
      all_goals try { rw [ite_eq_right (by have:=PE.encode_lt e; omega),ite_eq_left (by have:=PE.encode_lt e; omega),edge_third PS PA PE PR C marked ε h,h.destination] }
      all_goals try { rw [ite_eq_right (by omega),ite_eq_right (by omega)]; rfl }
    · intro c i a
      rcases c with (e|(e|e))|b
      all_goals simp only [comparison,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,Data.affine,h.edges]
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_first PS PA PE PR C marked ε h]; exact h.domain e i a }
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_second PS PA PE PR C marked ε h]; exact h.domain e i a }
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_third PS PA PE PR C marked ε h]; exact h.domain e i a }
      all_goals try { rw [ite_eq_right (by omega)]; have hb : PE.bound+(PE.bound+PE.bound)+PR.encode b-3*PE.bound=PR.encode b := by omega
                      rw [hb]; exact h.requestDomain b i a }
    · intro c i a
      rcases c with (e|(e|e))|b
      all_goals simp only [comparison,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,Data.affine,h.edges]
      all_goals try { rw [ite_eq_right (by have:=PE.encode_lt e; omega)]<;> rfl }
      all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; exact ⟨by omega,by omega⟩),edge_third PS PA PE PR C marked ε h]; exact h.map e i a }
      all_goals try { rw [ite_eq_right (by  omega)]; rfl }
  · intro p
    rcases p with (s|a)|(e|u)
    all_goals simp only [Data.affine,Data.gates,h.scalars,h.ands,h.edges,real,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,Presentation.unit_encode,
      Circuit.Description.realDimension,Circuit.dimension]
    · rw [ite_eq_left (PS.encode_lt s)]
    · rw [ite_eq_right (by omega),ite_eq_left (by have:=PA.encode_lt a; omega)]
    · rw [ite_eq_right (by  omega),ite_eq_left (by have:=PE.encode_lt e; change PS.bound+PA.bound+_<_; omega)]
    · rw [ite_eq_right (by  omega),ite_eq_right (by  omega)]
  · intro c
    rcases c with (e|(e|e))|b
    all_goals simp only [Data.affine,h.edges,comparison,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,Circuit.Description.consistency]
    · rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_first PS PA PE PR C marked ε h]; exact output_form PS PA PE PR C marked ε h e
    · rw [ite_eq_left (by have:=PE.encode_lt e; omega),edge_second PS PA PE PR C marked ε h]; exact output_form PS PA PE PR C marked ε h e
    · rw [ite_eq_right (by omega),ite_eq_left (by have:=PE.encode_lt e; omega)]; rfl
    · rw [ite_eq_right (by  omega),ite_eq_right (by  omega)]; rfl
  · intro c
    rcases c with (e|(e|e))|b
    all_goals simp only [Data.affine,h.edges,comparison,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,Circuit.Description.consistency]
    · rw [ite_eq_left (PE.encode_lt e)]; rfl
    · rw [ite_eq_right (by omega),ite_eq_left (by have:=PE.encode_lt e; omega)]; rfl
    · rw [ite_eq_right (by omega),ite_eq_right (by have:=PE.encode_lt e; omega),ite_eq_left (by have:=PE.encode_lt e; omega),edge_third PS PA PE PR C marked ε h,h.destinationForm]; rfl
    · rw [ite_eq_right (by  omega),ite_eq_right (by  omega),ite_eq_right (by  omega)]; rfl
  · intro c; rfl
  · intro c
    rcases c with (e|(e|e))|b
    all_goals simp only [Data.affine,h.edges,comparison,Presentation.sum_inl,Presentation.sum_inr,Presentation.sum_bound,]
    all_goals try { rw [ite_eq_left (by have:=PE.encode_lt e; omega)]<;> rfl }
    rw [ite_eq_right (by  omega)]
    have hb : PE.bound+(PE.bound+PE.bound)+PR.encode b-3*PE.bound=PR.encode b := by  omega
    rw [hb,h.requestTest]
    cases C.requestTest b <;> rfl
end VariableWL.CircuitCatalog

namespace VariableWL.BlockCatalog.Data
theorem ext_fields {X Y : Data} (h1 : X.rows=Y.rows) (h2 : X.internal=Y.internal)
    (h3 : X.reals=Y.reals) (h4 : X.comparisons=Y.comparisons)
    (h5 : X.validReal=Y.validReal) (h6 : X.validComparison=Y.validComparison)
    (h7 : X.source=Y.source) (h8 : X.target=Y.target) (h9 : X.domain=Y.domain) (h10 : X.map=Y.map) : X=Y := by
  cases X; cases Y; simp_all
end VariableWL.BlockCatalog.Data
namespace VariableWL.AffineCatalog.Data
theorem ext_fields {X Y : Data} (h1 : X.toData=Y.toData) (h2 : X.realDimension=Y.realDimension)
    (h3 : X.leftForm=Y.leftForm) (h4 : X.rightForm=Y.rightForm)
    (h5 : X.leftConstant=Y.leftConstant) (h6 : X.rightConstant=Y.rightConstant)
    (h7 : X.marked=Y.marked) (h8 : X.epsilon=Y.epsilon) : X=Y := by
  cases X; cases Y; simp_all
end VariableWL.AffineCatalog.Data

end OAI
