import OAI.NumberTheory.Ostmann.Tree.CycleLocalMajorantsCoefficients
import OAI.NumberTheory.Ostmann.Tree.QuartetFactorization

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Tree.CycleQuartet
open QuartetFactorization Ostmann.FiniteField
variable {p : ℕ} [Fact p.Prime] {k b : ℕ}

theorem frame_parameters_fixed (T : Diagram (ZMod p) (k+2))
    (M : Leaves (k+2) → (ZMod p)ˣ) (fs : Leaves k → Frame (ZMod p))
    (hf : ancestorFrames T M = some fs) (v : Leaves k) :
    (frameDiagram T M fs hf v).parameters = bottomParameters k T.parameters v :=
  (propagate_validity k T.parameters T.consistent T.rootLeft T.rootRight
    (Density.rootCoefficient T.parameters) (Density.rootCoefficient_consistent _)
    ((bottomCut k).project M) fs hf v).1

theorem frame_familyRoot (T : Diagram (ZMod p) (k+2))
    (M : Leaves (k+2) → (ZMod p)ˣ) (fs : Leaves k → Frame (ZMod p))
    (hf : ancestorFrames T M = some fs) (v : Leaves k) :
    (frameDiagram T M fs hf v).localNode.familyRoot ((bottomCut k).project M v) =
      (fs v).argument T.denominator ((bottomCut k).project M v) := by
  have he := Diagram.localNode_rootArgument (frameDiagram T M fs hf v) (bottomLeaves k M v)
  rw [bottomLeaves_product k M v] at he
  exact he.trans (frameDiagram_rootArgument T M fs hf v)

variable (P : LeafPartition (k+2) b)
  (c : BalancedSelection P.label (quartetCut k).label)

theorem frame_actionCoefficient_bound (T : Diagram (ZMod p) (k+2))
    (M : Leaves (k+2) → (ZMod p)ˣ) (fs : Leaves k → Frame (ZMod p))
    (hf : ancestorFrames T M = some fs) (g : ZMod p → ℂ) (hg0 : g 0=0)
    (v : Leaves k) (ρ : MulChar (ZMod p) ℂ) :
    let totals := (bottomCut k).project M
    let Ts := frameDiagram T M fs hf
    letI : ∀v,MulAction (ZMod p)ˣ (ProductFiber (totals v)) := fun v => fiberMulAction P c v (totals v)
    Density.average (fun m : ProductFiber (totals v) =>
      ‖actionCoefficient (fiberValues Ts g totals) v ρ m‖^2) ≤
      localMajorant P c (bottomParameters k T.parameters) g v ρ
        ((fs v).argument T.denominator (totals v)) := by
  let totals := (bottomCut k).project M
  let Ts := frameDiagram T M fs hf
  let : ∀v,MulAction (ZMod p)ˣ (ProductFiber (totals v)) := fun v => fiberMulAction P c v (totals v)
  have hb := actionCoefficient_fiber_bound P c (bottomParameters k T.parameters) Ts
    (frame_parameters_fixed T M fs hf) g hg0 totals v ρ
  have hy : (Ts v).localNode.familyRoot (totals v) =
      (fs v).argument T.denominator (totals v) := frame_familyRoot T M fs hf v
  rw [hy] at hb
  exact hb

end Ostmann.Tree.CycleQuartet
end

end OAI
