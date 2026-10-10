import OAI.NumberTheory.Ostmann.Tree.CycleProjection
import OAI.NumberTheory.Ostmann.Tree.CycleQuartets

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators ComplexConjugate
open Ostmann.FiniteField Ostmann.Arithmetic.ResidueHaar
variable {p : ℕ} [Fact p.Prime]

abbrev CoupledLeaves {d b : ℕ} (P Q : LeafPartition d b) :=
  {x : (Leaves d → (ZMod p)ˣ) × (Leaves d → (ZMod p)ˣ) // P.coupled Q x}

instance coupledLeavesFintype {d b : ℕ} (P Q : LeafPartition d b) :
    Fintype (CoupledLeaves (p:=p) P Q) := Fintype.ofFinite _

def diagramCorrelation {d b : ℕ} (P Q : LeafPartition d b)
    (T1 T2 : Diagram (ZMod p) d) (g : ZMod p → ℂ) : ℂ :=
  average (fun x : CoupledLeaves (p:=p) P Q => T1.value g x.val.1*conj (T2.value g x.val.2))

def coupledLeavesEquiv {d b : ℕ} (P Q : LeafPartition d b) :
    coupledGroup (labelProducts (U:=(ZMod p)ˣ) P.label) (labelProducts Q.label) ≃
      CoupledLeaves (p:=p) P Q where
  toFun x := ⟨x.val,fun i => congrFun x.property i⟩
  invFun x := ⟨x.val,funext x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem diagramCorrelation_projection_sq {k b : ℕ} (P Q : LeafPartition (k+2) b)
    (c : BalancedSelection P.label (quartetCut k).label)
    (T1 T2 : Diagram (ZMod p) (k+2)) (g : ZMod p → ℂ) :
    ‖diagramCorrelation P Q T1 T2 g‖^2≤
      Density.average (fun M => ‖c.projection (T1.value g) M‖^2)*
        Density.average (fun M => ‖T2.value g M‖^2) := by
  classical
  have hc := cycle_projection_reduction Q.label P.onto Q.onto c (T1.value g) (T2.value g)
  have he := average_equiv (coupledLeavesEquiv (p:=p) P Q)
    (fun x : CoupledLeaves (p:=p) P Q => T1.value g x.val.1*conj (T2.value g x.val.2))
  change average (fun x : coupledGroup (labelProducts P.label) (labelProducts Q.label) =>
    T1.value g x.val.1*conj (T2.value g x.val.2))=diagramCorrelation P Q T1 T2 g at he
  rw [he] at hc
  simp only [real_average_fintype_congr _
    (inferInstance : Fintype (Leaves (k+2) → (ZMod p)ˣ))] at hc
  exact hc

end
end Ostmann.Tree

end OAI
