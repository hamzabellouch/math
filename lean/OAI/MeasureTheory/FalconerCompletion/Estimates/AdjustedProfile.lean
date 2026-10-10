import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Estimates.TreeCenter
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphPerp

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace
variable {d : ℕ}

noncomputable def adjustedProfile (m : ℝ → ℝ) (N : ℕ) (n : ℕ) : ℝ :=
  m n-(d:ℝ)/2*(n:ℝ)/N

noncomputable def testWidth (N J i n : ℕ) (sig : ℝ) : ℝ :=
  (2-(i:ℝ)/J)*(2:ℝ)^(-(n:ℝ))*((2:ℝ)^N)^(500*sig)

noncomputable def fullParallelCount (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (g p : ℕ) (P : CellPath d) (W : ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℕ :=
  ((dyadicPaths p).filter fun Q => 0 < ρ (treeCell Q) ∧
    dist (treeCenter Q) (treeCenter P) < 10*(d+1)/(2:ℝ)^g ∧
    ‖graphPerpND w (treeCenter Q-treeCenter P)‖ ≤ W).card

lemma fullParallelCount_actual_line (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (g p : ℕ) (P : CellPath d) (W : ℝ) (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖=1) :
    fullParallelCount ρ g p P W w =
      ((dyadicPaths p).filter fun Q => 0 < ρ (treeCell Q) ∧
        dist (treeCenter Q) (treeCenter P) < 10*(d+1)/(2:ℝ)^g ∧
        infDist (treeCenter Q) (graphAffineLineND w (treeCenter P)) ≤ W).card := by
  simp only [fullParallelCount,infDist_graphAffineLineND w _ _ hw]

end CurrentFalconer.TreeND
end
end

end OAI
