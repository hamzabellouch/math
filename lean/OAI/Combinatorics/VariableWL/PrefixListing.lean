import OAI.Combinatorics.VariableWL.PrefixDescriptor

namespace OAI

universe uVariable1

namespace VariableWL.PrefixDescriptor.Data
attribute [local instance] Classical.propDecidable
variable (D : Data) (x y : Raw) (i j : ℕ)
theorem treeValid_true : D.treeValid x=true ↔
    (D.root x.block x.channel≤x.height ∧ x.height≤D.dimension x.block) ∧
    (List.range PrefixAlphabet.vectorCount).any (fun z=>D.legal x.block z &&
      decide (PrefixAlphabet.prefixCode (D.order x.block x.channel) x.height z=x.vector))=true := by
  simp only [treeValid,Bool.and_eq_true,decide_eq_true_eq]
theorem validRaw_true : D.validRaw x=true ↔ D.validBlock x.block=true ∧
    ((x.kind=0 ∧ x.channel=0 ∧ x.height=0 ∧ x.vector=0) ∨
      (x.kind=1 ∧ x.channel<D.channels x.block ∧ x.height=0) ∧ D.legal x.block x.vector=true ∨
      (x.kind=2 ∧ x.channel<D.channels x.block) ∧ D.treeValid x=true) := by
  simp only [validRaw,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,or_assoc]
theorem sortValid_true : D.sortValid x=true ↔ D.validBlock x.block=true ∧
    ((x.kind=0 ∧ x.channel=0 ∧ x.height=0) ∨
      (x.kind=1 ∧ x.channel<D.channels x.block ∧ x.height=0) ∨
      (x.kind=2 ∧ x.channel<D.channels x.block ∧ D.root x.block x.channel≤x.height ∧
        x.height≤D.dimension x.block)) := by
  simp only [sortValid,Bool.and_eq_true,decide_eq_true_eq]
theorem forward_true : D.forward x y=true ↔
    (x.kind=0 ∧ y.kind=2 ∧ y.channel=0 ∧ y.height=0) ∨
    (x.kind=1 ∧ y.kind=1 ∧ x.channel+1=y.channel ∧ x.vector=y.vector) ∨
    (x.kind=2 ∧ y.kind=2 ∧ x.channel=y.channel ∧ x.height+1=y.height ∧
      PrefixAlphabet.trim x.height y.vector=x.vector) ∨
    (x.kind=2 ∧ y.kind=1 ∧ x.channel=y.channel ∧ x.height=D.dimension x.block ∧
      x.vector=PrefixAlphabet.prefixCode (D.order x.block y.channel) (D.dimension x.block) y.vector) := by
  simp only [forward,Bool.or_eq_true,decide_eq_true_eq,or_assoc]
theorem internal_true : D.internal x y i j=true ↔
    (x.block=y.block ∧ (D.forward x y=true ∨ D.forward y x=true)) ∧
    (i=D.slot x y ∧ j=D.slot y x) := by
  simp only [internal,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
theorem roots_true : D.roots x y i j=true ↔
    ((x.kind=2 ∧ y.kind=2 ∧ i=0 ∧ j=0 ∧ x.channel≠0 ∧ y.channel≠0 ∧
      x.height=D.root x.block x.channel ∧ y.height=D.root y.block y.channel) ∧
      D.matching (x.block*D.channelBound+x.channel) (y.block*D.channelBound+y.channel)=true) ∧
      PrefixAlphabet.paddedEqual x.vector y.vector=true := by
  simp only [roots,Bool.and_eq_true,decide_eq_true_eq]
theorem anchors_true : D.anchors x y i j=true ↔
    x.kind=0 ∧ y.kind=0 ∧
    ((i=2 ∧ j=1 ∧ Descriptor.rank D.validBlock x.block+1=Descriptor.rank D.validBlock y.block) ∨
      (i=1 ∧ j=2 ∧ Descriptor.rank D.validBlock y.block+1=Descriptor.rank D.validBlock x.block)) := by
  simp only [anchors,decide_eq_true_eq]
end VariableWL.PrefixDescriptor.Data

namespace VariableWL.Computation.Stack.PolyRecipe
open Recipe
variable {n : ℕ}
theorem underOne_number (P : Expr (n+1)) (v : Env n) (a b : Word) :
    (underOne P).number (cons a (cons b v))=P.number (cons a v) := by
  change ((underOne P).value _).length=_
  rw [underOne_value]
  rfl
theorem underTwo_number (P : Expr (n+2)) (v : Env n) (a b c : Word) :
    (underTwo P).number (cons a (cons b (cons c v)))=P.number (cons a (cons b v)) := by
  change ((underTwo P).value _).length=_
  rw [underTwo_value]
  rfl
end VariableWL.Computation.Stack.PolyRecipe

namespace VariableWL.PrefixAlphabet.TotalProgram
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}
noncomputable def paddedEqual (I J : Expr n) : Expr n :=
  choose (conj (lt I (numeral vectorCount)) (lt J (numeral vectorCount)))
    (Program.paddedEqual I J) (literal [false])
 theorem paddedEqual_bit (I J : Expr n) (v : Env n) :
    (paddedEqual I J).bit v=PrefixAlphabet.paddedEqual (I.number v) (J.number v) := by
  simp only [paddedEqual,choose_bit,conj_bit,lt_bit,numeral_number,Bool.and_eq_true,decide_eq_true_eq]
  split_ifs with h
  · exact Program.paddedEqual_bit _ _ _ h.1 h.2
  · have hf : (literal [false] : Expr n).bit v=false := rfl
    rw [hf]
    unfold PrefixAlphabet.paddedEqual
    by_cases hi : I.number v<vectorCount
    · have hj : ¬J.number v<vectorCount := fun hj=>h ⟨hi,hj⟩
      rw [dite_eq_left hi,dite_eq_right hj]
    · rw [dite_eq_right hi]
end VariableWL.PrefixAlphabet.TotalProgram

namespace VariableWL.PrefixDescriptor.Program
attribute [local instance] Classical.propDecidable
open Computation.Stack.PolyRecipe Computation.Stack.Recipe
variable {n : ℕ}

structure RawExpr (n : ℕ) where
  block : Expr n
  kind : Expr n
  channel : Expr n
  height : Expr n
  vector : Expr n

def RawExpr.eval (x : RawExpr n) (v : Env n) : Raw :=
  ⟨x.block.number v,x.kind.number v,x.channel.number v,x.height.number v,x.vector.number v⟩
def RawExpr.up (x : RawExpr n) : RawExpr (n+1) :=
  ⟨x.block.up,x.kind.up,x.channel.up,x.height.up,x.vector.up⟩
theorem RawExpr.eval_up (x : RawExpr n) (v : Env n) (a : Word) : x.up.eval (cons a v)=x.eval v := rfl

structure Listing (n : ℕ) where
  blocks : Expr n
  validBlock : Expr (n+1)
  channelBound : Expr n
  dimension : Expr (n+1)
  channels : Expr (n+1)
  root : Expr (n+2)
  order : Expr (n+2)
  legal : Expr (n+2)
  matching : Expr (n+2)

namespace Listing
variable (D : Listing n)
def eval (v : Env n) : Data where
  blocks := D.blocks.number v
  validBlock i := D.validBlock.bit (cons (List.replicate i true) v)
  channelBound := D.channelBound.number v
  dimension i := D.dimension.number (cons (List.replicate i true) v)
  channels i := D.channels.number (cons (List.replicate i true) v)
  root i j := D.root.number (cons (List.replicate i true) (cons (List.replicate j true) v))
  order i j := D.order.number (cons (List.replicate i true) (cons (List.replicate j true) v))
  legal i j := D.legal.bit (cons (List.replicate i true) (cons (List.replicate j true) v))
  matching i j := D.matching.bit (cons (List.replicate i true) (cons (List.replicate j true) v))
def up : Listing (n+1) where
  blocks := D.blocks.up
  validBlock := underOne D.validBlock
  channelBound := D.channelBound.up
  dimension := underOne D.dimension
  channels := underOne D.channels
  root := underTwo D.root
  order := underTwo D.order
  legal := underTwo D.legal
  matching := underTwo D.matching

theorem eval_up (v : Env n) (a : Word) : D.up.eval (cons a v)=D.eval v := by
  unfold eval up
  congr 1
  · funext i; exact underOne_bit ..
  · funext i; exact underOne_number ..
  · funext i; exact underOne_number ..
  · funext i j; exact underTwo_number ..
  · funext i j; exact underTwo_number ..
  · funext i j; exact underTwo_bit ..
  · funext i j; exact underTwo_bit ..

noncomputable def sortBound : Expr n := mul (mul (mul D.blocks (numeral 3)) D.channelBound) (numeral 7)
noncomputable def bound : Expr n := mul D.sortBound (numeral PrefixAlphabet.vectorCount)
noncomputable def tag (x : RawExpr n) : Expr n :=
  add (mul (add (mul (add (mul x.block (numeral 3)) x.kind) D.channelBound) x.channel) (numeral 7)) x.height
noncomputable def unpack (I : Expr n) : RawExpr n :=
  let a := div I (numeral PrefixAlphabet.vectorCount)
  let b := div a (numeral 7)
  let c := div b D.channelBound
  ⟨div c (numeral 3),mod c (numeral 3),mod b D.channelBound,mod a (numeral 7),
    mod I (numeral PrefixAlphabet.vectorCount)⟩
 theorem sortBound_number (v : Env n) : D.sortBound.number v=(D.eval v).sortBound := by
  simp only [sortBound,mul_number,numeral_number,Data.sortBound,eval]
 theorem bound_number (v : Env n) : D.bound.number v=(D.eval v).bound := by
  simp only [bound,mul_number,numeral_number,sortBound_number,Data.bound]
 theorem tag_number (x : RawExpr n) (v : Env n) : (D.tag x).number v=(D.eval v).tag (x.eval v) := by
  simp only [tag,add_number,mul_number,numeral_number,Data.tag,RawExpr.eval,eval]
 theorem unpack_eval (I : Expr n) (v : Env n) : (D.unpack I).eval v=(D.eval v).unpack (I.number v) := by
  simp only [unpack,RawExpr.eval,div_number,mod_number,numeral_number,Data.unpack,eval]

noncomputable def treePossible (x : RawExpr n) (J : Expr n) : Expr n :=
  conj (applyNat₂ D.legal x.block J)
    (eq (PrefixAlphabet.TotalProgram.prefixCode (applyNat₂ D.order x.block x.channel) x.height J) x.vector)
noncomputable def treeValid (x : RawExpr n) : Expr n :=
  conj (conj (le (applyNat₂ D.root x.block x.channel) x.height) (le x.height (applyNat D.dimension x.block)))
    (any (numeral PrefixAlphabet.vectorCount) (D.up.treePossible x.up (input 0)))
noncomputable def validRaw (x : RawExpr n) : Expr n :=
  conj (applyNat D.validBlock x.block)
    (disj (conj (conj (eq x.kind (numeral 0)) (eq x.channel (numeral 0)))
      (conj (eq x.height (numeral 0)) (eq x.vector (numeral 0))))
    (disj (conj (conj (conj (eq x.kind (numeral 1)) (lt x.channel (applyNat D.channels x.block)))
        (eq x.height (numeral 0))) (applyNat₂ D.legal x.block x.vector))
      (conj (conj (eq x.kind (numeral 2)) (lt x.channel (applyNat D.channels x.block))) (D.treeValid x))))
noncomputable def valid (I : Expr n) : Expr n := D.validRaw (D.unpack I)

 theorem treePossible_bit (x : RawExpr n) (J : Expr n) (v : Env n) :
    (D.treePossible x J).bit v=((D.eval v).legal (x.eval v).block (J.number v) &&
      decide (PrefixAlphabet.prefixCode ((D.eval v).order (x.eval v).block (x.eval v).channel)
        (x.eval v).height (J.number v)=(x.eval v).vector)) := by
  simp only [treePossible,conj_bit,applyNat₂_bit,eq_bit,PrefixAlphabet.TotalProgram.prefixCode_number,applyNat₂_number]
  rfl
 theorem treeValid_bit (x : RawExpr n) (v : Env n) :
    (D.treeValid x).bit v=(D.eval v).treeValid (x.eval v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.treeValid_true]
  simp only [treeValid,conj_bit,le_bit,applyNat₂_number,applyNat_number,any_bit,numeral_number,
    treePossible_bit,eval_up,RawExpr.eval_up,input_number,cons_zero,List.length_replicate]
  dsimp only [eval,RawExpr.eval]
  simp only [Bool.and_eq_true,decide_eq_true_eq]
 theorem validRaw_bit (x : RawExpr n) (v : Env n) :
    (D.validRaw x).bit v=(D.eval v).validRaw (x.eval v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.validRaw_true]
  simp only [validRaw,conj_bit,disj_bit,eq_bit,lt_bit,applyNat_bit,applyNat_number,applyNat₂_bit,
    numeral_number,treeValid_bit,RawExpr.eval,eval]
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  simp only [and_assoc]
 theorem valid_bit (I : Expr n) (v : Env n) :
    (D.valid I).bit v=(D.eval v).valid (I.number v) := by
  rw [valid,validRaw_bit,unpack_eval]
  rfl

noncomputable def sortValid (x : RawExpr n) : Expr n :=
  conj (applyNat D.validBlock x.block)
    (disj (conj (eq x.kind (numeral 0)) (conj (eq x.channel (numeral 0)) (eq x.height (numeral 0))))
      (disj (conj (eq x.kind (numeral 1)) (conj (lt x.channel (applyNat D.channels x.block)) (eq x.height (numeral 0))))
        (conj (eq x.kind (numeral 2)) (conj (lt x.channel (applyNat D.channels x.block))
          (conj (le (applyNat₂ D.root x.block x.channel) x.height) (le x.height (applyNat D.dimension x.block)))))))
noncomputable def sortPredicate (I : Expr n) : Expr n := D.sortValid (D.unpack (mul I (numeral PrefixAlphabet.vectorCount)))
noncomputable def color (I : Expr n) : Expr n := add (numeral 1)
  (count (D.tag (D.unpack I)) (D.up.sortPredicate (input 0)))
noncomputable def colorBound : Expr n := add (numeral 1) (count D.sortBound (D.up.sortPredicate (input 0)))
 theorem sortValid_bit (x : RawExpr n) (v : Env n) :
    (D.sortValid x).bit v=(D.eval v).sortValid (x.eval v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.sortValid_true]
  simp only [sortValid,conj_bit,disj_bit,eq_bit,lt_bit,le_bit,applyNat_bit,applyNat_number,applyNat₂_number,
    numeral_number,RawExpr.eval,eval]
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
 theorem sortPredicate_bit (I : Expr n) (v : Env n) :
    (D.sortPredicate I).bit v=(D.eval v).sortPredicate (I.number v) := by
  rw [sortPredicate,sortValid_bit,unpack_eval,mul_number,numeral_number]
  rfl
 theorem color_number (I : Expr n) (v : Env n) :
    (D.color I).number v=(D.eval v).color (I.number v) := by
  simp only [color,add_number,numeral_number,count_number,tag_number,unpack_eval,sortPredicate_bit,
    eval_up,input_number,cons_zero,List.length_replicate]
  rfl
 theorem colorBound_number (v : Env n) : D.colorBound.number v=(D.eval v).colorBound := by
  simp only [colorBound,add_number,numeral_number,count_number,sortBound_number,sortPredicate_bit,
    eval_up,input_number,cons_zero,List.length_replicate]
  rfl

noncomputable def forward (x y : RawExpr n) : Expr n :=
  disj (disj (disj
    (conj (conj (eq x.kind (numeral 0)) (eq y.kind (numeral 2)))
      (conj (eq y.channel (numeral 0)) (eq y.height (numeral 0))))
    (conj (conj (eq x.kind (numeral 1)) (eq y.kind (numeral 1)))
      (conj (eq (add x.channel (numeral 1)) y.channel) (eq x.vector y.vector))))
    (conj (conj (eq x.kind (numeral 2)) (eq y.kind (numeral 2)))
      (conj (eq x.channel y.channel) (conj (eq (add x.height (numeral 1)) y.height)
        (eq (PrefixAlphabet.TotalProgram.trim x.height y.vector) x.vector)))))
    (conj (conj (eq x.kind (numeral 2)) (eq y.kind (numeral 1)))
      (conj (eq x.channel y.channel) (conj (eq x.height (applyNat D.dimension x.block))
        (eq x.vector (PrefixAlphabet.TotalProgram.prefixCode (applyNat₂ D.order x.block y.channel)
          (applyNat D.dimension x.block) y.vector)))))
noncomputable def slot (x y : RawExpr n) : Expr n :=
  choose (eq x.kind (numeral 0)) (numeral 0)
    (choose (eq x.kind (numeral 1))
      (choose (eq y.kind (numeral 1)) (choose (lt y.channel x.channel) (numeral 0) (numeral 1)) (numeral 2))
      (choose (eq y.kind (numeral 0)) (numeral 0)
        (choose (eq y.kind (numeral 1)) (numeral 1)
          (choose (lt y.height x.height) (numeral 0)
            (choose (lt x.height (applyNat D.dimension x.block))
              (add (PrefixAlphabet.TotalProgram.bit y.vector x.height) (numeral 1)) (numeral 1))))))
noncomputable def internal (x y : RawExpr n) (I J : Expr n) : Expr n :=
  conj (conj (eq x.block y.block) (disj (D.forward x y) (D.forward y x)))
    (conj (eq I (D.slot x y)) (eq J (D.slot y x)))
 theorem forward_bit (x y : RawExpr n) (v : Env n) :
    (D.forward x y).bit v=(D.eval v).forward (x.eval v) (y.eval v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.forward_true]
  simp only [forward,conj_bit,disj_bit,eq_bit,add_number,numeral_number,applyNat_number,applyNat₂_number,
    PrefixAlphabet.TotalProgram.trim_number,PrefixAlphabet.TotalProgram.prefixCode_number,
    RawExpr.eval,eval]
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  simp only [and_assoc,or_assoc]
 theorem slot_number (x y : RawExpr n) (v : Env n) :
    (D.slot x y).number v=(D.eval v).slot (x.eval v) (y.eval v) := by
  simp only [slot,NumericProgram.choose_number,eq_bit,lt_bit,add_number,numeral_number,applyNat_number,
    PrefixAlphabet.TotalProgram.bit_number,decide_eq_true_eq,Data.slot,RawExpr.eval,eval]
  rfl
 theorem internal_bit (x y : RawExpr n) (I J : Expr n) (v : Env n) :
    (D.internal x y I J).bit v=(D.eval v).internal (x.eval v) (y.eval v) (I.number v) (J.number v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.internal_true]
  simp only [internal,conj_bit,disj_bit,eq_bit,forward_bit,slot_number,RawExpr.eval]
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]

noncomputable def roots (x y : RawExpr n) (I J : Expr n) : Expr n :=
  conj (conj (conj (conj (eq x.kind (numeral 2)) (eq y.kind (numeral 2)))
    (conj (conj (eq I (numeral 0)) (eq J (numeral 0)))
      (conj (conj (neg (eq x.channel (numeral 0))) (neg (eq y.channel (numeral 0))))
        (conj (eq x.height (applyNat₂ D.root x.block x.channel)) (eq y.height (applyNat₂ D.root y.block y.channel))))))
    (applyNat₂ D.matching (add (mul x.block D.channelBound) x.channel) (add (mul y.block D.channelBound) y.channel)))
    (PrefixAlphabet.TotalProgram.paddedEqual x.vector y.vector)
noncomputable def anchors (x y : RawExpr n) (I J : Expr n) : Expr n :=
  conj (conj (eq x.kind (numeral 0)) (eq y.kind (numeral 0)))
    (disj (conj (conj (eq I (numeral 2)) (eq J (numeral 1)))
      (eq (add (count x.block D.validBlock) (numeral 1)) (count y.block D.validBlock)))
      (conj (conj (eq I (numeral 1)) (eq J (numeral 2)))
        (eq (add (count y.block D.validBlock) (numeral 1)) (count x.block D.validBlock))))
noncomputable def incidence (I J : Expr n) : Expr n :=
  let x := D.unpack (div I (numeral 3))
  let y := D.unpack (div J (numeral 3))
  let i := mod I (numeral 3)
  let j := mod J (numeral 3)
  disj (disj (D.internal x y i j) (D.roots x y i j)) (D.anchors x y i j)
 theorem roots_bit (x y : RawExpr n) (I J : Expr n) (v : Env n) :
    (D.roots x y I J).bit v=(D.eval v).roots (x.eval v) (y.eval v) (I.number v) (J.number v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.roots_true]
  simp only [roots,conj_bit,eq_bit,neg_bit,applyNat₂_number,applyNat₂_bit,add_number,mul_number,
    numeral_number,PrefixAlphabet.TotalProgram.paddedEqual_bit,RawExpr.eval,eval,
    ]
  simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not]
  simp only [and_assoc]
 theorem anchors_bit (x y : RawExpr n) (I J : Expr n) (v : Env n) :
    (D.anchors x y I J).bit v=(D.eval v).anchors (x.eval v) (y.eval v) (I.number v) (J.number v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Data.anchors_true]
  simp only [anchors,conj_bit,disj_bit,eq_bit,add_number,numeral_number,count_number,
    RawExpr.eval,eval,Descriptor.rank]
  simp only [Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  simp only [and_assoc]
 theorem incidence_bit (I J : Expr n) (v : Env n) :
    (D.incidence I J).bit v=(D.eval v).incidence (I.number v) (J.number v) := by
  simp only [incidence,disj_bit,internal_bit,roots_bit,anchors_bit,unpack_eval,div_number,mod_number,numeral_number]
  rfl

noncomputable def portListing : PortListing n where
  bound := D.bound
  valid := D.up.valid (input 0)
  color := D.up.color (input 0)
  colorBound := D.colorBound
  incidence := D.up.up.incidence (input 0) (input 1)
 theorem portListing_eval (v : Env n) : D.portListing.eval v=(D.eval v).portData := by
  unfold PortListing.eval Data.portData
  dsimp only [portListing]
  apply Descriptor.PortData.ext
  all_goals dsimp only
  · exact D.bound_number v
  · funext i; simp only [valid_bit,eval_up,input_number,cons_zero,List.length_replicate ]
  · funext i; simp only [color_number,eval_up,input_number,cons_zero,List.length_replicate ]
  · exact D.colorBound_number v
  · funext i j; simp only [incidence_bit,eval_up,input_number,cons_zero,show (1 : Fin (n+2))=(0 : Fin (n+1)).succ from rfl,cons_succ,List.length_replicate ]
end Listing
end VariableWL.PrefixDescriptor.Program

namespace VariableWL.Descriptor.Presentation
variable {A : Type uVariable1} [Fintype A] (P : Presentation A)
 theorem enumeration_val (x : A) :
    ((@VariableWL.enumeration A _ P.numbering) x).val=Descriptor.rank P.valid (P.encode x) := rfl
end VariableWL.Descriptor.Presentation

end OAI
