import OAI.NumberTheory.Ostmann.Tree.QuartetFactorizationArguments
import OAI.NumberTheory.Ostmann.Tree.QuartetFactorizationFibers
import OAI.NumberTheory.Ostmann.Tree.QuartetFactorizationValidity

namespace OAI

namespace Ostmann.Tree.QuartetFactorization
noncomputable section
open scoped BigOperators
open Density
variable {F : Type*} [Field F]

def ancestorFrames {k : ℕ} (T : Diagram F (k+2)) (M : Leaves (k+2) → Fˣ) :
    Option (Leaves k → Frame F) :=
  propagate k T.parameters T.rootLeft T.rootRight (Density.rootCoefficient T.parameters)
    ((bottomCut k).project M)

theorem ancestorFrames_eq_of_project_eq {k : ℕ} (T : Diagram F (k+2))
    (M N : Leaves (k+2) → Fˣ)
    (h : (bottomCut k).project M = (bottomCut k).project N) :
    ancestorFrames T M = ancestorFrames T N := by
  unfold ancestorFrames
  rw [h]

theorem diagram_factorization {k : ℕ} (T : Diagram F (k+2))
    (g : F → ℂ) (M : Leaves (k+2) → Fˣ) :
    T.value g M = frameProduct g T.denominator (bottomLeaves k M) (ancestorFrames T M) := by
  exact evaluate_factorization k T.parameters g T.denominator T.rootLeft T.rootRight
    (Density.rootCoefficient T.parameters) 0 M

theorem diagram_value_zero_of_invalid {k : ℕ} (T : Diagram F (k+2))
    (g : F → ℂ) (M : Leaves (k+2) → Fˣ) (h : ancestorFrames T M = none) :
    T.value g M = 0 := by
  rw [diagram_factorization, h]
  rfl

def frameDiagram {k : ℕ} (T : Diagram F (k+2)) (M : Leaves (k+2) → Fˣ)
    (fs : Leaves k → Frame F) (h : ancestorFrames T M = some fs) (v : Leaves k) :
    Diagram F 2 where
  parameters := (fs v).parameters
  denominator := T.denominator
  rootLeft := (fs v).leftCurrent
  rootRight := (fs v).rightCurrent
  consistent := by
    have hp := (propagate_validity k T.parameters T.consistent T.rootLeft T.rootRight
      (Density.rootCoefficient T.parameters) (Density.rootCoefficient_consistent _)
      ((bottomCut k).project M) fs h v).1
    rw [hp]
    exact bottomParameters_consistent k T.parameters T.consistent v
  bottomOpposite := by
    have hp := (propagate_validity k T.parameters T.consistent T.rootLeft T.rootRight
      (Density.rootCoefficient T.parameters) (Density.rootCoefficient_consistent _)
      ((bottomCut k).project M) fs h v).1
    rw [hp]
    exact bottomParameters_bottomOpposite k T.parameters T.bottomOpposite v

theorem diagram_value_eq_product {k : ℕ} (T : Diagram F (k+2))
    (g : F → ℂ) (M : Leaves (k+2) → Fˣ) (fs : Leaves k → Frame F)
    (h : ancestorFrames T M = some fs) :
    T.value g M = ∏ v, (frameDiagram T M fs h v).value g (bottomLeaves k M v) := by
  rw [diagram_factorization, h]
  rfl

theorem diagramLevelArguments_eq_frameArguments {k : ℕ} (T : Diagram F (k+2))
    (M : Leaves (k+2) → Fˣ) :
    Density.diagramLevelArguments (bottomCut k) T M =
      frameArguments T.denominator ((bottomCut k).project M) (ancestorFrames T M) := by
  exact (propagate_arguments k T.parameters T.denominator T.rootLeft T.rootRight
    (Density.rootCoefficient T.parameters) ((bottomCut k).project M)).symm

theorem ancestorFrames_isSome {k : ℕ} (T : Diagram F (k+2))
    (M : Leaves (k+2) → Fˣ) :
    (ancestorFrames T M).isSome =
      (Density.diagramLevelArguments (bottomCut k) T M).isSome := by
  rw [diagramLevelArguments_eq_frameArguments]
  cases ancestorFrames T M <;> rfl

theorem frameDiagram_rootArgument {k : ℕ} (T : Diagram F (k+2))
    (M : Leaves (k+2) → Fˣ) (fs : Leaves k → Frame F)
    (h : ancestorFrames T M = some fs) (v : Leaves k) :
    Density.rootArgument (frameDiagram T M fs h v).parameters T.denominator
      (fs v).leftCurrent (fs v).rightCurrent
      (Density.rootCoefficient (frameDiagram T M fs h v).parameters)
      (bottomLeaves k M v) = (fs v).argument T.denominator ((bottomCut k).project M v) := by
  have hc := (propagate_validity k T.parameters T.consistent T.rootLeft T.rootRight
    (Density.rootCoefficient T.parameters) (Density.rootCoefficient_consistent _)
    ((bottomCut k).project M) fs h v).2
  change Density.rootArgument (fs v).parameters T.denominator
    (fs v).leftCurrent (fs v).rightCurrent (Density.rootCoefficient (fs v).parameters)
    (bottomLeaves k M v) = _
  rw [← Frame.coefficient_eq_rootCoefficient (fs v) hc]
  exact (frame_argument_actual_leaves k T.denominator M fs v).symm

theorem diagram_value_on_productFiber {k : ℕ} (T : Diagram F (k+2))
    (g : F → ℂ) (totals : Leaves k → Fˣ)
    (m : (v : Leaves k) → {z : Leaves 2 → Fˣ // Parameters.leafProduct z = totals v}) :
    T.value g ((productFiberEquiv k totals).symm m).val =
      match propagate k T.parameters T.rootLeft T.rootRight
          (Density.rootCoefficient T.parameters) totals with
      | none => 0
      | some fs => ∏ v, (fs v).value g T.denominator (m v).val := by
  rw [diagram_factorization]
  unfold ancestorFrames
  rw [((productFiberEquiv k totals).symm m).property]
  have hLeaves : bottomLeaves k ((productFiberEquiv k totals).symm m).val =
      (fun v => (m v).val) := bottomLeaves_assemble k _
  rw [hLeaves]
  rfl

end
end Ostmann.Tree.QuartetFactorization

end OAI
