import OAI.MeasureTheory.Falconer.Incidence.ComparableFrozenPencils
import OAI.MeasureTheory.Falconer.Estimates.RetainedRegularCells
import OAI.MeasureTheory.Falconer.Geometry.RetainedCoarseCover
import OAI.MeasureTheory.Falconer.Estimates.RegularCellConfiguration

namespace OAI

/-! The finite data retained by the regular-set scale argument. Every point
and fine line is a member of the original configuration. -/
namespace Falconer
open scoped BigOperators

structure RegularRefinementData (n : ℕ) (s t D : ℝ)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) where
  cells : Finset (Space 2)
  pencils : Space 2 → Finset (Space 2)
  points : Space 2 → Finset (Space 2)
  fine : Space 2 → Finset (Space 2)
  packets : Space 2 → Finset (Space 2)
  width : ℝ
  level : ℕ
  width_pos : 0 < width
  cells_nonempty : cells.Nonempty
  cells_chart : InBoundedLineChart cells
  cells_regular : NormalizedFiniteBallBound (1/(2:ℝ)^(n+3)) t D cells
  pencil_data : ∀ c ∈ cells, width/D ≤ ((pencils c).card:ℝ) ∧
    ((pencils c).card:ℝ) ≤ D*width ∧ InBoundedLineChart (pencils c) ∧
    FiniteSeparatedAt (1/(2:ℝ)^(n+3)) (pencils c) ∧
    NormalizedFiniteBallBound (1/(2:ℝ)^(n+3)) s D (pencils c) ∧
    ∀ l ∈ pencils c, TubeIncident (1/(2:ℝ)^(n+3)) c l
  point_data : ∀ c ∈ cells, points c ⊆ P.filter (fun p => coarsePlanarRound (1/(2:ℝ)^(n+3)) p = c) ∧
    (points c).Nonempty ∧
    (∀ p ∈ points c, |p 0-c 0| ≤ (1/(2:ℝ)^n)/4 ∧ |p 1-c 1| ≤ (1/(2:ℝ)^n)/4) ∧
    NormalizedFiniteBallBound (1/(2:ℝ)^n) t D
      ((points c).image (localPacketPoint (1/(2:ℝ)^n) (c 0) (c 1)))
  point_mass : (P.card:ℝ) ≤ D*((cells.biUnion points).card:ℝ)
  fine_data : ∀ c ∈ cells, ∀ p ∈ points c, fine p ⊆ V p ∧
    1/(D*((1/(2:ℝ)^n)^s)^2) ≤ ((fine p).card:ℝ) ∧
    ((fine p).card:ℝ) ≤ D/((1/(2:ℝ)^n)^s)^2 ∧
    NormalizedFiniteBallBound ((1/(2:ℝ)^n)^2) s D (fine p)
  packet_cover : ∀ c ∈ cells, ∀ p ∈ points c, ∀ l ∈ fine p, ∃ a ∈ pencils c, l ∈ packets a
  packet_sum : (∑ a ∈ cells.biUnion pencils, ((packets a).card:ℝ)) ≤ 13*((P.biUnion V).card:ℝ)
  packet_band : ∀ a ∈ cells.biUnion pencils, 2^level ≤ (packets a).card ∧ (packets a).card < 2^(level+1)
  coarse_cover : ((((cells.biUnion points).biUnion fine).image
    (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤ 13*((cells.biUnion pencils).card:ℝ)

end Falconer

end OAI
