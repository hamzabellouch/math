import OAI.NumberTheory.Ostmann.Tree.CycleQuartetActionsSelected

namespace OAI

noncomputable section
namespace Ostmann.Tree.CycleQuartet

def position (a b : Bool) : Leaves 2 := Fin.cons a (Fin.cons b Fin.elim0)

@[simp] theorem position_zero (a b : Bool) : position a b 0=a := rfl
@[simp] theorem position_one (a b : Bool) : position a b 1=b := rfl

@[simp] theorem position_eq_iff (a b x y : Bool) : position a b=position x y ↔ a=x ∧ b=y := by
  constructor
  · intro h
    exact ⟨congrFun h 0,congrFun h 1⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem position_eta (w : Leaves 2) : position (w 0) (w 1)=w := by
  funext i
  fin_cases i <;> rfl

theorem exists_position (w : Leaves 2) : ∃a b,w=position a b :=
  ⟨w 0,w 1,(position_eta w).symm⟩

variable {F : Type*} [Field F]

theorem twoLeafAct_swap (u v : Leaves 2) (z : Fˣ) (M : Leaves 2 → Fˣ) :
    twoLeafAct v u z M=twoLeafAct u v z⁻¹ M := by
  funext w
  simp only [twoLeafAct,inv_inv]
  rw [mul_comm (if w=v then z else 1) (if w=u then z⁻¹ else 1)]

theorem twoLeafAct_cross (a b : Bool) (z : Fˣ) (M : Leaves 2 → Fˣ) :
    twoLeafAct (position false a) (position true b) z M=Quartet.moveCross M a b z := by
  funext w
  obtain ⟨x,y,rfl⟩ := exists_position w
  cases a <;> cases b <;> cases x <;> cases y <;>
    simp [twoLeafAct,Quartet.moveCross,Quartet.scalePair,Quartet.scaleLeaf,
      Density.join,Density.left,Density.right,position,mul_comm]

theorem twoLeafAct_same (a : Bool) (z : Fˣ) (M : Leaves 2 → Fˣ) :
    twoLeafAct (position a false) (position a true) z M=Quartet.NodeInput.moveSame M a z := by
  funext w
  obtain ⟨x,y,rfl⟩ := exists_position w
  cases a <;> cases x <;> cases y <;>
    simp [twoLeafAct,Quartet.NodeInput.moveSame,Quartet.movePair,Quartet.scaleLeaf,
      Density.join,Density.left,Density.right,position,mul_comm]

inductive Kind where
  | same (side inverse : Bool)
  | cross (leftLeaf rightLeaf inverse : Bool)
  deriving DecidableEq

def Kind.act (kind : Kind) (z : Fˣ) (M : Leaves 2 → Fˣ) : Leaves 2 → Fˣ :=
  match kind with
  | .same side inverse => Quartet.NodeInput.moveSame M side (if inverse then z⁻¹ else z)
  | .cross a b inverse => Quartet.moveCross M a b (if inverse then z⁻¹ else z)

def classifyPositions (u v : Leaves 2) : Kind :=
  match u 0,v 0 with
  | false,false => .same false (u 1)
  | true,true => .same true (u 1)
  | false,true => .cross (u 1) (v 1) false
  | true,false => .cross (v 1) (u 1) true

theorem twoLeafAct_classify (u v : Leaves 2) (huv : u≠v) (z : Fˣ) (M : Leaves 2 → Fˣ) :
    twoLeafAct u v z M=(classifyPositions u v).act z M := by
  obtain ⟨a,b,rfl⟩ := exists_position u
  obtain ⟨x,y,rfl⟩ := exists_position v
  cases a <;> cases b <;> cases x <;> cases y
  all_goals try exact False.elim (huv rfl)
  all_goals simp only [classifyPositions,position_zero,position_one,Kind.act,
    Bool.false_eq_true,ite_false,ite_true]
  all_goals first
    | exact twoLeafAct_same _ _ _
    | exact twoLeafAct_cross _ _ _ _
    | rw [twoLeafAct_swap,twoLeafAct_same]
    | rw [twoLeafAct_swap,twoLeafAct_cross]

variable {k b : ℕ} (P : LeafPartition (k+2) b)
  (c : BalancedSelection P.label (quartetCut k).label)

def kind (v : cycleQuartets P c) : Kind :=
  classifyPositions (positivePosition P c v) (negativePosition P c v)

theorem localAct_eq_kind (v : cycleQuartets P c) (z : Fˣ) (M : Leaves 2 → Fˣ) :
    localAct P c v.val z M=(kind P c v).act z M := by
  rw [localAct_eq_twoLeafAct]
  exact twoLeafAct_classify _ _ (positions_distinct P c v) z M

end Ostmann.Tree.CycleQuartet

end

end OAI
