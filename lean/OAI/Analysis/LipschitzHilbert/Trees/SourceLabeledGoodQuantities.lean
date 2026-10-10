import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledMainTail
import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledErrorPhysicalTail

namespace OAI

/-! Joint measurability of the actual reference quantities is needed
before weighted bad-path sets are integrated over the physical plane. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert

theorem lineEnvelope_continuous (a l : ℝ) (n : ℕ) : Continuous (lineEnvelope a l n) := by
  apply Continuous.inv₀
  · fun_prop
  · intro x
    positivity

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem physicalMainScale_joint_continuous (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) :
    Continuous (fun z : ℝ×ℝ => P.physicalMainScale t a b v g j z.2 z.1) := by
  apply continuous_finsetSum
  intro l _
  apply continuous_finsetSum
  intro u _
  apply Continuous.mul continuous_const
  exact ((lineEnvelope_continuous _ _ _).comp continuous_fst).mul
    ((lineEnvelope_continuous _ _ _).comp continuous_snd)

theorem physicalMainSquare_joint_continuous (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    Continuous (fun z : ℝ×ℝ => P.physicalMainSquare t a b v g z.2 z.1) := by
  apply Continuous.sqrt
  exact continuous_finsetSum _ (fun j _ =>
    (P.physicalMainScale_joint_continuous t a b v g j).pow 2)

def physicalMainSquareOnPlane (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (z : ℝ×ℝ) : ℝ :=
  P.physicalMainSquare t a b v g (z.2-t*z.1) z.1

theorem physicalMainSquareOnPlane_continuous (t a : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    Continuous (P.physicalMainSquareOnPlane t a b v g) := by
  let shear : ℝ×ℝ → ℝ×ℝ := fun z => (z.1,z.2-t*z.1)
  have hs : Continuous shear :=
    continuous_fst.prodMk (continuous_snd.sub (continuous_const.mul continuous_fst))
  have h := (P.physicalMainSquare_joint_continuous t a b v g).comp hs
  change Continuous ((fun z : ℝ×ℝ =>
    P.physicalMainSquare t a b v g z.2 z.1) ∘ shear)
  exact h

theorem measurableSet_error_or_main (t a threshold : ℝ)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    MeasurableSet {z | threshold ≤ P.physicalAngularError t a b v g z ∨
      threshold ≤ P.physicalMainSquareOnPlane t a b v g z} := by
  exact (measurableSet_le measurable_const (P.physicalAngularError_measurable t a b v g)).union
    (measurableSet_le measurable_const (P.physicalMainSquareOnPlane_continuous t a b v g).measurable)

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
