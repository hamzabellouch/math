import OAI.NumberTheory.Ostmann.Tree.Fourier

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators ComplexConjugate

abbrev Leaves (depth : ℕ) := Fin depth → Bool

inductive Parameters (F : Type*) [Field F] : ℕ → Type _
  | leaf (frequency : Fˣ) (conjugated : Bool) : Parameters F 0
  | branch {depth : ℕ} (frequency leftConstant rightConstant splitConstant : Fˣ)
      (left right : Parameters F depth) : Parameters F (depth+1)

namespace Parameters
variable {F : Type*} [Field F]
local instance : DecidableEq F := Classical.decEq F

def frequency : {depth : ℕ} → Parameters F depth → Fˣ
  | _, .leaf s _ => s
  | _, .branch s _ _ _ _ _ => s

def childConsistent (target : Fˣ) : {depth : ℕ} → Parameters F depth → Prop
  | _, .leaf _ _ => True
  | _, .branch _ a b _ _ _ => a*b=target

def consistent : {depth : ℕ} → Parameters F depth → Prop
  | _, .leaf _ _ => True
  | _, .branch _ a b u left right =>
      childConsistent (u*a) left ∧ childConsistent (u*b) right ∧
      consistent left ∧ consistent right

def bottomOpposite : {depth : ℕ} → Parameters F depth → Prop
  | _, .leaf _ _ => True
  | 1, .branch _ _ _ _ (.leaf _ a) (.leaf _ b) => a ≠ b
  | _+2, .branch _ _ _ _ left right => bottomOpposite left ∧ bottomOpposite right

def childLeaves {depth : ℕ} (M : Leaves (depth+1) → Fˣ) (side : Bool) :
    Leaves depth → Fˣ := fun v => M (Fin.cons side v)

def leafProduct {depth : ℕ} (M : Leaves depth → Fˣ) : Fˣ := ∏ v, M v

def evaluate (g : F → ℂ) (D : Fˣ) : {depth : ℕ} → Parameters F depth →
    Fˣ → Fˣ → F → (Leaves depth → Fˣ) → ℂ
  | _, .leaf _ c, _, _, incoming, _ => if c then conj (g incoming) else g incoming
  | _, .branch s a b u left right, Xleft, Xright, _, M =>
      let Ml := childLeaves M false
      let Mr := childLeaves M true
      let Hl := Xleft*a*leafProduct Ml
      let Hr := Xright*b*leafProduct Mr
      let pivot : F := ((left.frequency : F)*Hr-(right.frequency : F)*Hl) / ((s : F)*u)
      if hp : pivot=0 then 0 else
        let P : Fˣ := Units.mk0 pivot hp
        let yl : F := (left.frequency : F)/((D : F)*P*u*Hl)
        let yr : F := (right.frequency : F)/((D : F)*P*u*Hr)
        evaluate g D left P Xleft yl Ml * evaluate g D right P Xright yr Mr

def value (g : F → ℂ) (D Xleft Xright : Fˣ) :
    {depth : ℕ} → Parameters F depth → (Leaves depth → Fˣ) → ℂ
  | 0, .leaf s c, M =>
      let y : F := (s : F) / M (fun i => Fin.elim0 i)
      if c then conj (g y) else g y
  | _+1, P, M => evaluate g D P Xleft Xright 0 M

end Parameters

structure Diagram (F : Type*) [Field F] (depth : ℕ) where
  parameters : Parameters F depth
  denominator : Fˣ
  rootLeft : Fˣ
  rootRight : Fˣ
  consistent : parameters.consistent
  bottomOpposite : parameters.bottomOpposite

namespace Diagram
variable {F : Type*} [Field F] {depth : ℕ}
def value (T : Diagram F depth) (g : F → ℂ) (M : Leaves depth → Fˣ) : ℂ :=
  T.parameters.value g T.denominator T.rootLeft T.rootRight M
end Diagram

structure LeafPartition (depth blocks : ℕ) where
  label : Leaves depth → Fin blocks
  onto : Function.Surjective label

namespace LeafPartition
variable {F : Type*} [Field F] {depth blocks : ℕ}
def componentProduct (P : LeafPartition depth blocks) (M : Leaves depth → Fˣ)
    (b : Fin blocks) : Fˣ := ∏ i with P.label i = b, M i

def coupled (P Q : LeafPartition depth blocks)
    (M : (Leaves depth → Fˣ) × (Leaves depth → Fˣ)) : Prop :=
  ∀ b, P.componentProduct M.1 b = Q.componentProduct M.2 b

end LeafPartition
end
end Ostmann.Tree

end OAI
