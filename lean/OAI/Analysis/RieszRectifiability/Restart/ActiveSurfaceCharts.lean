import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveSurfaceChartStep

namespace OAI

/-!
# Active-cell chart predicates

Input charts parametrize a larger tangential disk and capture the surface near an active cell.
Surface charts retain exact tangential coordinates on a smaller disk together with quantitative
normal slope, height, and local image bounds. These predicates package the geometric data used
to propagate charts through the active projection construction.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R} {k : ℕ}
  {z : (supportLatticeNets μ R hR k).points}

def HasActiveCellSurfaceChart (q : SupportCellDescendant μ R hR k z)
    (S : AffineSubspace ℝ (Ambient d)) (ε : ℝ) (A : Set (Ambient d)) : Prop :=
  ∃ h : closedBall (S.direction.orthogonalProjectionOnto q.center) ((5 / 2 : ℝ) * q.radius) → Ambient d,
    LipschitzWith 2 h ∧
    LipschitzWith (Real.toNNReal (4 * activeProjectionError d ε))
      (fun u => (S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (h u)) ∧
    (∀ u, h u ∈ A ∧ S.direction.orthogonalProjectionOnto (h u) = u.val ∧
      infDist (h u) (S : Set (Ambient d)) ≤ (262144 * ε) * q.radius ∧
      h u ∈ closedBall q.center (3 * q.radius)) ∧
    A ∩ closedBall q.center ((9 / 4 : ℝ) * q.radius) =
      Set.range h ∩ closedBall q.center ((9 / 4 : ℝ) * q.radius)

def HasActiveCellInputChart (q : SupportCellDescendant μ R hR k z)
    (S : AffineSubspace ℝ (Ambient d)) (A : Set (Ambient d)) : Prop :=
  ∃ g : closedBall (S.direction.orthogonalProjectionOnto q.center) ((11 / 4 : ℝ) * q.radius) → Ambient d,
    LipschitzWith 2 g ∧
    (∀ u, S.direction.orthogonalProjectionOnto (g u) = u.val) ∧
    (∀ u, g u ∈ closedBall q.center (3 * q.radius)) ∧
    Set.range g ⊆ A ∧
    A ∩ closedBall q.center ((5 / 2 : ℝ) * q.radius) ⊆ Set.range g

def HasActiveSurfaceCharts (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) (t : ℕ)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (ε : ℝ) (A : Set (Ambient d)) : Prop :=
  ∀ q ∈ activeLevelIndex μ R hR k z Good t, HasActiveCellSurfaceChart q (S q) ε A

theorem HasActiveCellSurfaceChart.height_on_inner_ball
    (q : SupportCellDescendant μ R hR k z) (S : AffineSubspace ℝ (Ambient d))
    (ε : ℝ) (A : Set (Ambient d)) (hchart : HasActiveCellSurfaceChart q S ε A)
    (x : Ambient d) (hx : x ∈ A) (hnear : x ∈ closedBall q.center ((9 / 4 : ℝ) * q.radius)) :
    infDist x (S : Set (Ambient d)) ≤ (262144 * ε) * q.radius := by
  obtain ⟨h, _, _, hcoords, hcapture⟩ := hchart
  have hin : x ∈ Set.range h := (hcapture ▸ (show x ∈ A ∩ closedBall q.center
    ((9 / 4 : ℝ) * q.radius) from ⟨hx, hnear⟩)).1
  obtain ⟨u, rfl⟩ := hin
  exact (hcoords u).2.2.1

end

end RieszRectifiability

end OAI
