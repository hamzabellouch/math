import OAI.Geometry.IsometricImmersion.Darboux.DarbouxEquation
import OAI.Geometry.IsometricImmersion.Estimates.HighFactorOrders

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

abbrev DarbouxState := Fin 6 → ℝ

def statePoint (w : DarbouxState) : Coord := ![w 0, w 1]
def stateGradient (w : DarbouxState) : Coord := ![w 2, w 3]
def stateBaseDomain (U : Set Coord) : Set DarbouxState := statePoint ⁻¹' U

def stateConnection (g : MetricField) (i j : Fin 2) (w : DarbouxState) : ℝ :=
  jetConnection g (statePoint w) i j (stateGradient w)

def stateMixed (g : MetricField) (w : DarbouxState) : ℝ :=
  jetMixed g (statePoint w) (w 4) (stateGradient w)

def stateDenominator (g : MetricField) (w : DarbouxState) : ℝ :=
  jetYY g (statePoint w) (w 5) (stateGradient w)

def stateEnergy (g : MetricField) (w : DarbouxState) : ℝ :=
  jetEnergy g (statePoint w) (stateGradient w)

def stateNumerator (g : MetricField) (w : DarbouxState) : ℝ :=
  jetNumerator g (statePoint w) (w 4) (stateGradient w)

def darbouxStateDomain (g : MetricField) (U : Set Coord) : Set DarbouxState :=
  {w | statePoint w ∈ U ∧ stateDenominator g w ≠ 0}

def sixVariableP (g : MetricField) (w : DarbouxState) : ℝ :=
  solvedDarboux g (statePoint w) (w 4) (w 5) (stateGradient w)

theorem statePoint_contDiff : ContDiff ℝ ∞ statePoint := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ (0 : Fin 6)
  · exact contDiff_apply ℝ ℝ (1 : Fin 6)

theorem stateGradient_contDiff : ContDiff ℝ ∞ stateGradient := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ (2 : Fin 6)
  · exact contDiff_apply ℝ ℝ (3 : Fin 6)

theorem stateBaseDomain_isOpen {U : Set Coord} (hU : IsOpen U) :
    IsOpen (stateBaseDomain U) := hU.preimage statePoint_contDiff.continuous

variable {g : MetricField} {U : Set Coord}

theorem stateConnection_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (stateConnection g i j) (stateBaseDomain U) := by
  unfold stateConnection jetConnection
  apply ContDiffOn.sum
  intro r hr
  exact ((christoffel_contDiffOn hg hU r i j).comp statePoint_contDiff.contDiffOn
    (fun w hw => hw)).mul (((contDiff_apply ℝ ℝ r).comp stateGradient_contDiff).contDiffOn)

theorem stateMixed_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateMixed g) (stateBaseDomain U) :=
  (contDiffOn_apply ℝ ℝ 4 _).sub (stateConnection_contDiffOn hg hU 0 1)

theorem stateDenominator_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateDenominator g) (stateBaseDomain U) :=
  (contDiffOn_apply ℝ ℝ 5 _).sub (stateConnection_contDiffOn hg hU 1 1)

theorem stateEnergy_contDiffOn (hg : SmoothPositiveOn g U) :
    ContDiffOn ℝ ∞ (stateEnergy g) (stateBaseDomain U) := by
  have hcoef (i j : Fin 2) : ContDiffOn ℝ ∞ (fun w => g (statePoint w) i j) (stateBaseDomain U) :=
    (hg.1 i j).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have hdet : ContDiffOn ℝ ∞ (fun w => (g (statePoint w)).det) (stateBaseDomain U) :=
    (metricDet_contDiffOn hg).comp statePoint_contDiff.contDiffOn (fun w hw => hw)
  have hv (i : Fin 2) : ContDiffOn ℝ ∞ (fun w => stateGradient w i) (stateBaseDomain U) :=
    ((contDiff_apply ℝ ℝ i).comp stateGradient_contDiff).contDiffOn
  exact hdet.sub ((((hcoef 1 1).mul ((hv 0).pow 2)).sub
    ((((hcoef 0 1).add (hcoef 1 0)).mul (hv 0)).mul (hv 1))).add
      ((hcoef 0 0).mul ((hv 1).pow 2)))

theorem stateNumerator_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateNumerator g) (stateBaseDomain U) :=
  ((stateMixed_contDiffOn hg hU).pow 2).add
    (((gaussianCurvature_contDiffOn hg hU).comp statePoint_contDiff.contDiffOn
      (fun _ hw => hw)).mul (stateEnergy_contDiffOn hg))

theorem darbouxStateDomain_isOpen (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    IsOpen (darbouxStateDomain g U) := by
  exact (stateDenominator_contDiffOn hg hU).continuousOn.isOpen_inter_preimage
    (stateBaseDomain_isOpen hU) isClosed_singleton.isOpen_compl

theorem sixVariableP_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (sixVariableP g) (darbouxStateDomain g U) := by
  have hsub : darbouxStateDomain g U ⊆ stateBaseDomain U := fun w hw => hw.1
  exact ((stateConnection_contDiffOn hg hU 0 0).mono hsub).add
    (((stateNumerator_contDiffOn hg hU).mono hsub).div
      ((stateDenominator_contDiffOn hg hU).mono hsub) (fun w hw => hw.2))

def solutionJet (z : Coord → ℝ) (p : Coord) : DarbouxState :=
  ![p 0, p 1, coordPartial 0 z p, coordPartial 1 z p,
    coordPartial 0 (coordPartial 1 z) p, coordPartial 1 (coordPartial 1 z) p]

theorem statePoint_solutionJet (z : Coord → ℝ) (p : Coord) :
    statePoint (solutionJet z p) = p := by
  ext i
  fin_cases i <;> rfl

theorem stateGradient_solutionJet (z : Coord → ℝ) (p : Coord) :
    stateGradient (solutionJet z p) = fun i => coordPartial i z p := by
  ext i
  fin_cases i <;> rfl

theorem stateDenominator_solutionJet (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    stateDenominator g (solutionJet z p) = covHessian g z p 1 1 := by
  unfold stateDenominator
  rw [statePoint_solutionJet, stateGradient_solutionJet]
  exact jetYY_at_height g p z

theorem sixVariableP_solutionJet (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    sixVariableP g (solutionJet z p) =
      solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p) := by
  unfold sixVariableP
  rw [statePoint_solutionJet, stateGradient_solutionJet]
  rfl

theorem solutionJet_contDiffOn {z : Coord → ℝ} (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (solutionJet z) U := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact contDiffOn_apply ℝ ℝ 0 U
  · exact contDiffOn_apply ℝ ℝ 1 U
  · exact partial_contDiffOn hz hU 0
  · exact partial_contDiffOn hz hU 1
  · exact partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0
  · exact partial_contDiffOn (partial_contDiffOn hz hU 1) hU 1

theorem solutionJet_mem_domain (g : MetricField) (z : Coord → ℝ) {p : Coord}
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0) :
    solutionJet z p ∈ darbouxStateDomain g U := by
  constructor
  · simpa only [statePoint_solutionJet] using hp
  · simpa only [stateDenominator_solutionJet] using hyy

end SmoothLocal.HighEquation

end

end OAI
