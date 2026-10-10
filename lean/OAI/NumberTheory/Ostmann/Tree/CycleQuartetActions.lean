import OAI.NumberTheory.Ostmann.Tree.CycleQuartetActionsCoordinates

namespace OAI

noncomputable section
namespace Ostmann.Tree.CycleQuartet
open QuartetFactorization
variable {k b : ℕ} (P : LeafPartition (k+2) b)
  (c : BalancedSelection P.label (quartetCut k).label)

def cycleQuartets : Finset (Leaves k) := c.positive.image (quartetCut k).label

theorem cycleQuartets_nonempty : (cycleQuartets P c).Nonempty :=
  c.nonempty.image _

def localAct {U : Type*} [CommGroup U] (v : Leaves k) (z : U)
    (M : Leaves 2 → U) : Leaves 2 → U := fun w => c.twist z (leaf k v w)*M w

@[simp] theorem localAct_one {U : Type*} [CommGroup U] (v : Leaves k)
    (M : Leaves 2 → U) : localAct P c v 1 M=M := by
  funext w
  simp [localAct,BalancedSelection.twist]

theorem localAct_mul {U : Type*} [CommGroup U] (v : Leaves k) (z t : U)
    (M : Leaves 2 → U) : localAct P c v (z*t) M=localAct P c v z (localAct P c v t M) := by
  funext w
  simp only [localAct,c.twist_mul,mul_assoc]

theorem bottomLeaves_act {F : Type*} [Field F] (v : Leaves k) (z : Fˣ)
    (M : Leaves (k+2) → Fˣ) :
    bottomLeaves k (c.act z M) v=localAct P c v z (bottomLeaves k M v) := by
  funext w
  simp only [bottomLeaves_apply,localAct,BalancedSelection.act]

theorem localAct_product {F : Type*} [Field F] (v : Leaves k) (z : Fˣ)
    (M : Leaves 2 → Fˣ) :
    Parameters.leafProduct (localAct P c v z M)=Parameters.leafProduct M := by
  let A := assembleBottom k (fun _ => M)
  have hA : bottomLeaves k A v=M := congrFun (bottomLeaves_assemble k (fun _ => M)) v
  have hproj := quartet_cycle_project P c z A
  have hcut : Density.Cut.project (F := F) (quartetCut k) =
      Density.Cut.project (F := F) (bottomCut k) :=
    congrArg (fun C : Density.Cut (k+2) k => Density.Cut.project (F := F) C) (cut_unique _ _)
  rw [hcut] at hproj
  rw [←hA,←bottomLeaves_act,bottomLeaves_product,bottomLeaves_product]
  exact congrFun hproj v

abbrev ProductFiber {F : Type*} [Field F] (m : Fˣ) :=
  {M : Leaves 2 → Fˣ // Parameters.leafProduct M=m}

def fiberAct {F : Type*} [Field F] (v : Leaves k) (m : Fˣ) (z : Fˣ)
    (M : ProductFiber m) : ProductFiber m :=
  ⟨localAct P c v z M.val,(localAct_product P c v z M.val).trans M.property⟩

@[instance_reducible] def fiberMulAction {F : Type*} [Field F] (v : Leaves k) (m : Fˣ) :
    MulAction Fˣ (ProductFiber m) where
  smul := fiberAct P c v m
  one_smul M := Subtype.ext (localAct_one P c v M.val)
  mul_smul z t M := Subtype.ext (localAct_mul P c v z t M.val)

end Ostmann.Tree.CycleQuartet

end

end OAI
