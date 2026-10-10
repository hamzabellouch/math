import OAI.Geometry.IsometricImmersion.Darboux.SixVariableDarboux
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def solutionJetCurve (z : Coord → ℝ) (x : ℝ) : ℝ → DarbouxState :=
  fun y => solutionJet z ![x, y]

theorem verticalPoint_contDiff (x : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ => (![x, y] : Coord)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_id

theorem solutionJetCurve_contDiffAt {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : Coord) ∈ U) :
    ContDiffAt ℝ ∞ (solutionJetCurve z x) y :=
  ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).comp y
    (verticalPoint_contDiff x).contDiffAt

theorem sixVariableP_contDiffAt_solutionJet
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    ContDiffAt ℝ ∞ (sixVariableP g) (solutionJet z p) :=
  (sixVariableP_contDiffOn hg hU).contDiffAt
    ((darbouxStateDomain_isOpen hg hU).mem_nhds (solutionJet_mem_domain g z hp hyy))

theorem actualP_faaExpansion
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : (![x, y] : Coord) ∈ U) (hyy : covHessian g z ![x, y] 1 1 ≠ 0) (ell : ℕ) :
    iteratedDeriv ell (sixVariableP g ∘ solutionJetCurve z x) y =
      ∑ c : OrderedFinpartition ell,
        iteratedFDeriv ℝ c.length (sixVariableP g) (solutionJetCurve z x y)
          (fun j => iteratedDeriv (c.partSize j) (solutionJetCurve z x) y) := by
  exact iteratedDeriv_vcomp_eq_sum_orderedFinpartition
    (sixVariableP_contDiffAt_solutionJet hg hU hp hyy)
    (solutionJetCurve_contDiffAt hU hz hp)
    (le_of_lt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl ell))

theorem actualDarboux_faaExpansion
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hp : (![x, y] : Coord) ∈ U) (ell : ℕ) :
    iteratedDeriv ell (fun t => coordPartial 0 (coordPartial 0 z) ![x, t]) y =
      ∑ c : OrderedFinpartition ell,
        iteratedFDeriv ℝ c.length (sixVariableP g) (solutionJetCurve z x y)
          (fun j => iteratedDeriv (c.partSize j) (solutionJetCurve z x) y) := by
  have heq : (fun t => coordPartial 0 (coordPartial 0 z) ![x, t]) =ᶠ[𝓝 y]
      sixVariableP g ∘ solutionJetCurve z x := by
    filter_upwards [(hU.preimage (verticalPoint_contDiff x).continuous).mem_nhds hp] with t ht
    change coordPartial 0 (coordPartial 0 z) ![x, t] = sixVariableP g (solutionJet z ![x, t])
    rw [sixVariableP_solutionJet]
    exact solvedDarboux_at_height hg hU hz ht (hyy _ ht) (hD _ ht)
  rw [heq.iteratedDeriv_eq ell]
  exact actualP_faaExpansion hg hU hz hp (hyy _ hp) ell

end SmoothLocal.HighEquation

end

end OAI
