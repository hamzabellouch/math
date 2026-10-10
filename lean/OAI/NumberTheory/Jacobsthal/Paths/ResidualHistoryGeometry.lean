import OAI.NumberTheory.Jacobsthal.Estimates.MovingLocalReference

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ResidualHistoryGeometry

attribute [local instance] Classical.propDecidable
open FinitePathGeometry PrimeHistories PrimeBinMembership PrimeTiltGeometry ActualPrimeHigh ActualBoundaryDomain
open SourceNodeCoordinates ReferenceResidualSum ReferenceSourceDecomposition
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem uncapped_gap_le {w : ℝ} {z : Node} {ps : List ℕ} (hp : uncappedAllowed w 2 z ps) :
    (terminal w z ps).gap ≤ z.gap := by
  induction ps generalizing z with
  | nil => exact le_rfl
  | cons p ps ih =>
    obtain ⟨hc,ht⟩ := hp
    have hx : 2 < primeExponent w p := (Finset.mem_filter.mp hc).2.1
    calc
      _ ≤ (step w z p).gap := ih (z:=step w z p) ht
      _ ≤ z.gap := sub_le_self _ (by linarith)

theorem source_terminal_geometry {B w : ℝ} (hB : 4 ≤ B) (start : Node)
    (hi : start.side=.even) (h199 : 199/100 ≤ start.ratio) (h23 : start.ratio ≤ 23/10)
    (hc : Consistent start) (hcut : start.cutoff=B) {ps : List ℕ} (hp : uncappedAllowed w 2 start ps) :
    Valid (terminal w start ps).side (terminal w start ps).ratio ∧
    Consistent (terminal w start ps) ∧ BoundaryDomain (terminal w start ps).side (terminal w start ps).gap ∧
    2 < (terminal w start ps).cutoff ∧ (terminal w start ps).cutoff ≤ B ∧
    0 < (terminal w start ps).gap ∧ (terminal w start ps).gap ≤ (23/10:ℝ)*B := by
  obtain ⟨hs,hr,_hBstart,hsize⟩ := source_node_bounds (by linarith : 0 < B) start hi h199 h23 hc hcut
  obtain ⟨U,_hU,hpU⟩ := (uncapped_iff_exists_ceiling w 2 start ps).mp hp
  refine ⟨terminal_valid hs hpU,terminal_consistent (by norm_num) hr hs hc hpU,
    source_boundary_domain hB le_rfl start hi h199 h23 hc hcut hp,
    uncapped_cutoff_gt_two (by rw [hcut]; linarith) hp,?_,uncapped_gap_positive (by norm_num) hr hs hp,
    (uncapped_gap_le hp).trans hsize⟩
  simpa only [hcut] using uncapped_cutoff_le hp

end NumberTheoryLean.ResidualHistoryGeometry

end

end Erdos970

end OAI
