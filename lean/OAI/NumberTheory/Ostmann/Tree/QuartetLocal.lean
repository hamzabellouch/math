import OAI.NumberTheory.Ostmann.Tree.DensityValues
import OAI.NumberTheory.Ostmann.Tree.QuartetSameBound

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Tree.Diagram
open Quartet Ostmann.FiniteField
variable {p : ℕ} [Fact p.Prime]

def localNode (T : Diagram (ZMod p) 2) : NodeInput (ZMod p) 1 :=
  NodeInput.ofDiagram T (fun _ => 1)

theorem localNode_parameters (T : Diagram (ZMod p) 2) :
    T.localNode.parameters = T.parameters := NodeInput.ofDiagram_parameters T _

theorem localNode_value (T : Diagram (ZMod p) 2) (g : ZMod p → ℂ)
    (M : Leaves 2 → (ZMod p)ˣ) :
    T.value g M = T.localNode.parameters.evaluate g T.localNode.D
      T.localNode.Xleft T.localNode.Xright 0 M := by
  cases he : T.parameters
  simp only [localNode, NodeInput.ofDiagram, NodeInput.ofParameters, he,
    NodeInput.parameters, Diagram.value, Parameters.value]

theorem localNode_rootArgument (T : Diagram (ZMod p) 2)
    (M : Leaves 2 → (ZMod p)ˣ) :
    T.localNode.familyRoot (Parameters.leafProduct M) =
      Density.rootArgument T.parameters T.denominator T.rootLeft T.rootRight
        (Density.rootCoefficient T.parameters) M := by
  cases he : T.parameters
  simp only [localNode, NodeInput.ofDiagram, NodeInput.ofParameters, he,
    NodeInput.familyRoot, Density.rootArgument, Density.rootCoefficient, Parameters.frequency]

theorem crossAction_fiber_bound (T : Diagram (ZMod p) 2) (g : ZMod p → ℂ)
    (hg0 : g 0=0) (a b : Bool) (m : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    Density.average (fun M : {M : Leaves 2 → (ZMod p)ˣ // Parameters.leafProduct M=m} =>
      ‖mellin (fun z : (ZMod p)ˣ => T.value g (moveCross M.val a b z)) ρ‖^2) ≤
      T.localNode.crossLocalMajorant g a b ρ (T.localNode.familyRoot m) := by
  simp_rw [localNode_value]
  exact NodeInput.crossAction_fiber_bound T.localNode
    (by rw [localNode_parameters]; exact T.consistent)
    (by rw [localNode_parameters]; exact T.bottomOpposite) g hg0 a b m ρ

theorem sameAction_fiber_bound (T : Diagram (ZMod p) 2) (g : ZMod p → ℂ)
    (hg0 : g 0=0) (side : Bool) (m : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    Density.average (fun M : {M : Leaves 2 → (ZMod p)ˣ // Parameters.leafProduct M=m} =>
      ‖mellin (fun z : (ZMod p)ˣ => T.value g (NodeInput.moveSame M.val side z)) ρ‖^2) ≤
      T.localNode.sameLocalMajorant g side ρ (T.localNode.familyRoot m) := by
  simp_rw [localNode_value]
  exact NodeInput.sameAction_fiber_bound T.localNode
    (by rw [localNode_parameters]; exact T.consistent)
    (by rw [localNode_parameters]; exact T.bottomOpposite) g hg0 side m ρ

theorem crossAction_inverse_fiber_bound (T : Diagram (ZMod p) 2) (g : ZMod p → ℂ)
    (hg0 : g 0=0) (a b : Bool) (m : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    Density.average (fun M : {M : Leaves 2 → (ZMod p)ˣ // Parameters.leafProduct M=m} =>
      ‖mellin (fun z : (ZMod p)ˣ => T.value g (moveCross M.val a b z⁻¹)) ρ‖^2) ≤
      T.localNode.crossLocalMajorant g a b ρ⁻¹ (T.localNode.familyRoot m) := by
  have he (M : Leaves 2 → (ZMod p)ˣ) :
      mellin (fun z : (ZMod p)ˣ => T.value g (moveCross M a b z⁻¹)) ρ =
      mellin (fun z : (ZMod p)ˣ => T.value g (moveCross M a b z)) ρ⁻¹ :=
    mellin_inverse_coordinate (fun z : (ZMod p)ˣ => T.value g (moveCross M a b z)) ρ
  simp_rw [he]
  exact crossAction_fiber_bound T g hg0 a b m ρ⁻¹

theorem sameAction_inverse_fiber_bound (T : Diagram (ZMod p) 2) (g : ZMod p → ℂ)
    (hg0 : g 0=0) (side : Bool) (m : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    Density.average (fun M : {M : Leaves 2 → (ZMod p)ˣ // Parameters.leafProduct M=m} =>
      ‖mellin (fun z : (ZMod p)ˣ => T.value g (NodeInput.moveSame M.val side z⁻¹)) ρ‖^2) ≤
      T.localNode.sameLocalMajorant g side ρ⁻¹ (T.localNode.familyRoot m) := by
  have he (M : Leaves 2 → (ZMod p)ˣ) :
      mellin (fun z : (ZMod p)ˣ => T.value g (NodeInput.moveSame M side z⁻¹)) ρ =
      mellin (fun z : (ZMod p)ˣ => T.value g (NodeInput.moveSame M side z)) ρ⁻¹ :=
    mellin_inverse_coordinate (fun z : (ZMod p)ˣ => T.value g (NodeInput.moveSame M side z)) ρ
  simp_rw [he]
  exact sameAction_fiber_bound T g hg0 side m ρ⁻¹

theorem untouched_fiber_bound (T : Diagram (ZMod p) 2) (g : ZMod p → ℂ)
    (hg0 : g 0=0) (m : (ZMod p)ˣ) :
    Density.average (fun M : {M : Leaves 2 → (ZMod p)ˣ // Parameters.leafProduct M=m} =>
      ‖T.value g M.val‖^2) ≤ T.localNode.untouchedLocalMajorant g (T.localNode.familyRoot m) := by
  simp_rw [localNode_value]
  exact NodeInput.untouched_fiber_bound T.localNode
    (by rw [localNode_parameters]; exact T.consistent)
    (by rw [localNode_parameters]; exact T.bottomOpposite) g hg0 m

end Ostmann.Tree.Diagram
end

end OAI
