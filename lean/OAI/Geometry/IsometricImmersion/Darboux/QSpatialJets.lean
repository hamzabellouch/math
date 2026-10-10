import OAI.Geometry.IsometricImmersion.Calculus.HorizontalJetCalculus
import OAI.Geometry.IsometricImmersion.Darboux.QPrincipal

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

def qSolutionJetCurve (z : Coord → ℝ) (y : ℝ) : ℝ → DarbouxState :=
  fun x => qSolutionJet z (coordinatePoint x y)

theorem qSolutionJet_contDiffOn {z : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (qSolutionJet z) U := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_apply ℝ ℝ 0 U
  · exact contDiffOn_apply ℝ ℝ 1 U
  · exact partial_contDiffOn hz hU 0
  · exact partial_contDiffOn hz hU 1
  · exact partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0
  · exact partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0

theorem qSolutionJetCurve_contDiffAt {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U) :
    ContDiffAt ℝ ∞ (qSolutionJetCurve z y) x :=
  ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).comp x
    (horizontalPoint_contDiff y).contDiffAt

theorem sixVariableQ_contDiffAt_solutionJet
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hxx : covHessian g z p 0 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sixVariableQ g) (qSolutionJet z p) :=
  (sixVariableQ_contDiffOn hg hU).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds (qSolutionJet_mem_domain hp hxx))

theorem qSolutionJetCurve_iteratedDeriv_positive
    {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U)
    (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n (qSolutionJetCurve z y) x =
      ![if n = 1 then 1 else 0, 0,
        spatialJet (spatialFirstJet z 0) n (coordinatePoint x y),
        spatialJet (spatialFirstJet z 1) n (coordinatePoint x y),
        spatialJet (spatialFirstJet z 1) (n + 1) (coordinatePoint x y),
        spatialJet (spatialFirstJet z 0) (n + 1) (coordinatePoint x y)] := by
  have hc := qSolutionJetCurve_contDiffAt hU hz hp
  ext i
  rw [iteratedDeriv_state_eval hc n i]
  fin_cases i
  · simpa [qSolutionJetCurve, qSolutionJet, coordinatePoint, hn.ne'] using
      (iteratedDeriv_fun_id (n := n) (x := x))
  · simp [qSolutionJetCurve, qSolutionJet, coordinatePoint, iteratedDeriv_const, hn.ne']
  · change iteratedDeriv n (fun t => coordPartial 0 z (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn hz hU 0) y n x hp,
      horizontalJet_eq_spatialJet]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 z (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn hz hU 1) y n x hp,
      horizontalJet_eq_spatialJet]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 1 z) (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0) y n x hp,
      horizontalJet_coordPartial hU (partial_contDiffOn hz hU 1) 0 n _ hp,
      horizontalJet_eq_spatialJet]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 0 z) (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0) y n x hp,
      horizontalJet_coordPartial hU (partial_contDiffOn hz hU 0) 0 n _ hp,
      horizontalJet_eq_spatialJet]
    rfl

theorem qSolutionJetCurve_iteratedDeriv
    {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : coordinatePoint x y ∈ U)
    (n : ℕ) (hn : 2 ≤ n) :
    iteratedDeriv n (qSolutionJetCurve z y) x =
      ![0, 0, coordPartial 0 (horizontalJet z n) (coordinatePoint x y),
        coordPartial 1 (horizontalJet z n) (coordinatePoint x y),
        coordPartial 0 (coordPartial 1 (horizontalJet z n)) (coordinatePoint x y),
        coordPartial 0 (coordPartial 0 (horizontalJet z n)) (coordinatePoint x y)] := by
  have hc := qSolutionJetCurve_contDiffAt hU hz hp
  ext i
  rw [iteratedDeriv_state_eval hc n i]
  fin_cases i
  · simp [qSolutionJetCurve, qSolutionJet, coordinatePoint, iteratedDeriv_fun_id,
      show n ≠ 0 by omega, show n ≠ 1 by omega]
  · simp [qSolutionJetCurve, qSolutionJet, coordinatePoint, iteratedDeriv_const,
      show n ≠ 0 by omega]
  · change iteratedDeriv n (fun t => coordPartial 0 z (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn hz hU 0) y n x hp,
      horizontalJet_coordPartial hU hz 0 n _ hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 1 z (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn hz hU 1) y n x hp,
      horizontalJet_coordPartial hU hz 1 n _ hp]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 1 z) (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0) y n x hp,
      horizontalJet_two_coordPartials hU hz hp n 0 1]
    rfl
  · change iteratedDeriv n (fun t => coordPartial 0 (coordPartial 0 z) (coordinatePoint t y)) x = _
    rw [horizontalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0) y n x hp,
      horizontalJet_two_coordPartials hU hz hp n 0 0]
    rfl

end SmoothLocal.HighEquation

end

end OAI
