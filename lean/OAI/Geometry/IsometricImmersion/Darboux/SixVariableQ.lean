import OAI.Geometry.IsometricImmersion.Darboux.SwappedDarboux
import OAI.Geometry.IsometricImmersion.Darboux.SixVariableLinearization

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

def qToPStateIndex (i : Fin 6) : Fin 6 := ![1, 0, 3, 2, 4, 5] i

def qToPState (w : DarbouxState) : DarbouxState := fun i => w (qToPStateIndex i)

def qToPStateLinear : DarbouxState →ₗ[ℝ] DarbouxState where
  toFun := qToPState
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def qToPStateCLM : DarbouxState →L[ℝ] DarbouxState :=
  LinearMap.toContinuousLinearMap qToPStateLinear

@[simp] theorem qToPStateCLM_apply (w : DarbouxState) : qToPStateCLM w = qToPState w := rfl

@[simp] theorem qToPStateIndex_involutive (i : Fin 6) :
    qToPStateIndex (qToPStateIndex i) = i := by
  fin_cases i <;> rfl

@[simp] theorem qToPState_involutive (w : DarbouxState) : qToPState (qToPState w) = w := by
  ext i
  exact congrArg w (qToPStateIndex_involutive i)

theorem qToPState_contDiff : ContDiff ℝ ∞ qToPState := qToPStateCLM.contDiff

theorem qToPState_hasFDerivAt (w : DarbouxState) :
    HasFDerivAt qToPState qToPStateCLM w := qToPStateCLM.hasFDerivAt

theorem qToPState_single (i : Fin 6) :
    qToPStateCLM (Pi.single i 1) = Pi.single (qToPStateIndex i) 1 := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [qToPStateCLM_apply, qToPState, qToPStateIndex]

@[simp] theorem statePoint_qToPState (w : DarbouxState) :
    statePoint (qToPState w) = coordinateSwap (statePoint w) := by
  ext i
  fin_cases i <;> simp [statePoint, qToPState, qToPStateIndex]

@[simp] theorem stateGradient_qToPState (w : DarbouxState) :
    stateGradient (qToPState w) = coordinateSwap (stateGradient w) := by
  ext i
  fin_cases i <;> simp [stateGradient, qToPState, qToPStateIndex]

@[simp] theorem qToPState_four (w : DarbouxState) : qToPState w 4 = w 4 := rfl
@[simp] theorem qToPState_five (w : DarbouxState) : qToPState w 5 = w 5 := rfl

def stateQDenominator (g : MetricField) (w : DarbouxState) : ℝ :=
  jetXX g (statePoint w) (w 5) (stateGradient w)

def darbouxQStateDomain (g : MetricField) (U : Set Coord) : Set DarbouxState :=
  {w | statePoint w ∈ U ∧ stateQDenominator g w ≠ 0}

def sixVariableQ (g : MetricField) : DarbouxState → ℝ :=
  sixVariableP (swappedMetric g) ∘ qToPState

theorem stateDenominator_qToPState {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    stateDenominator (swappedMetric g) (qToPState w) = stateQDenominator g w := by
  unfold stateDenominator
  rw [statePoint_qToPState, stateGradient_qToPState, qToPState_five]
  simpa only [stateQDenominator, coordinateSwap_involutive] using
    (jetYY_swappedMetric hg hU (p := coordinateSwap (statePoint w))
      (by simpa using hw) (w 5) (stateGradient w))

theorem sixVariableQ_explicit {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) :
    sixVariableQ g w =
      solvedDarbouxQ g (statePoint w) (w 4) (w 5) (stateGradient w) := by
  unfold sixVariableQ sixVariableP
  simp only [Function.comp_apply, statePoint_qToPState, stateGradient_qToPState,
    qToPState_four, qToPState_five]
  exact (solvedDarbouxQ_eq_swappedP hg hU hw (w 4) (w 5) (stateGradient w)).symm

theorem darbouxQStateDomain_eq_preimage {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    darbouxQStateDomain g U =
      qToPState ⁻¹' darbouxStateDomain (swappedMetric g) (coordinateSwap ⁻¹' U) := by
  ext w
  constructor
  · intro hw
    refine ⟨?_, ?_⟩
    · simpa only [Set.mem_preimage, statePoint_qToPState, coordinateSwap_involutive] using hw.1
    · simpa only [stateDenominator_qToPState hg hU hw.1] using hw.2
  · intro hw
    have hp : statePoint w ∈ U := by
      simpa only [Set.mem_preimage, statePoint_qToPState, coordinateSwap_involutive] using hw.1
    exact ⟨hp, by simpa only [stateDenominator_qToPState hg hU hp] using hw.2⟩

theorem qToPState_mem_domain {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    qToPState w ∈ darbouxStateDomain (swappedMetric g) (coordinateSwap ⁻¹' U) := by
  simpa only [darbouxQStateDomain_eq_preimage hg hU, Set.mem_preimage] using hw

theorem darbouxQStateDomain_isOpen {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) : IsOpen (darbouxQStateDomain g U) := by
  rw [darbouxQStateDomain_eq_preimage hg hU]
  exact (darbouxStateDomain_isOpen (swappedMetric_smoothPositive hg)
    (coordinateSwap_preimage_isOpen hU)).preimage qToPState_contDiff.continuous

theorem sixVariableQ_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (sixVariableQ g) (darbouxQStateDomain g U) :=
  (sixVariableP_contDiffOn (swappedMetric_smoothPositive hg)
    (coordinateSwap_preimage_isOpen hU)).comp qToPState_contDiff.contDiffOn
      (fun _ hw => qToPState_mem_domain hg hU hw)

theorem sixVariableQ_axis_eq_swappedP {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) (i : Fin 6) :
    fderiv ℝ (sixVariableQ g) w (Pi.single i 1) =
      fderiv ℝ (sixVariableP (swappedMetric g)) (qToPState w)
        (Pi.single (qToPStateIndex i) 1) := by
  have hp := qToPState_mem_domain hg hU hw
  have hP : DifferentiableAt ℝ (sixVariableP (swappedMetric g)) (qToPState w) :=
    ((sixVariableP_contDiffOn (swappedMetric_smoothPositive hg)
      (coordinateSwap_preimage_isOpen hU)).contDiffAt
        ((darbouxStateDomain_isOpen (swappedMetric_smoothPositive hg)
          (coordinateSwap_preimage_isOpen hU)).mem_nhds hp)).differentiableAt (by simp)
  rw [sixVariableQ, fderiv_comp w hP (qToPState_hasFDerivAt w).differentiableAt,
    (qToPState_hasFDerivAt w).fderiv, ContinuousLinearMap.comp_apply, qToPState_single]

theorem sixVariableQ_spatial_x {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    fderiv ℝ (sixVariableQ g) w (Pi.single 0 1) =
      fderiv ℝ (sixVariableP (swappedMetric g)) (qToPState w) (Pi.single 1 1) :=
  sixVariableQ_axis_eq_swappedP hg hU hw 0

theorem sixVariableQ_spatial_y {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    fderiv ℝ (sixVariableQ g) w (Pi.single 1 1) =
      fderiv ℝ (sixVariableP (swappedMetric g)) (qToPState w) (Pi.single 0 1) :=
  sixVariableQ_axis_eq_swappedP hg hU hw 1

theorem sixVariableQ_update_gradient {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) (i : Fin 2) (t : ℝ) :
    sixVariableQ g (Function.update w (gradientStateIndex i) t) =
      solvedDarbouxQ g (statePoint w) (w 4) (w 5)
        (Function.update (stateGradient w) i t) := by
  have hp : statePoint (Function.update w (gradientStateIndex i) t) = statePoint w := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [gradientStateIndex, statePoint]
  have hv : stateGradient (Function.update w (gradientStateIndex i) t) =
      Function.update (stateGradient w) i t := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [gradientStateIndex, stateGradient]
  rw [sixVariableQ_explicit hg hU (by simpa only [hp] using hw), hp, hv]
  fin_cases i <;> simp [gradientStateIndex]

theorem sixVariableQ_update_mixed {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) (t : ℝ) :
    sixVariableQ g (Function.update w 4 t) =
      solvedDarbouxQ g (statePoint w) t (w 5) (stateGradient w) := by
  have hp : statePoint (Function.update w 4 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 4 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  rw [sixVariableQ_explicit hg hU (by simpa only [hp] using hw), hp, hv]
  simp

theorem sixVariableQ_update_xx {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) (t : ℝ) :
    sixVariableQ g (Function.update w 5 t) =
      solvedDarbouxQ g (statePoint w) (w 4) t (stateGradient w) := by
  have hp : statePoint (Function.update w 5 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 5 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  rw [sixVariableQ_explicit hg hU (by simpa only [hp] using hw), hp, hv]
  simp

theorem sixVariableQ_gradient_axis {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) (i : Fin 2) :
    fderiv ℝ (sixVariableQ g) w (Pi.single (gradientStateIndex i) 1) =
      coordPartial i (solvedDarbouxQ g (statePoint w) (w 4) (w 5)) (stateGradient w) := by
  have hd := ((sixVariableQ_contDiffOn hg hU).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hd]
  have heq : (fun t => sixVariableQ g (Function.update w (gradientStateIndex i) t)) =
      (fun t => solvedDarbouxQ g (statePoint w) (w 4) (w 5)
        (Function.update (stateGradient w) i t)) :=
    funext (sixVariableQ_update_gradient hg hU hw.1 i)
  rw [heq]
  have hi : w (gradientStateIndex i) = stateGradient w i := by
    fin_cases i <;> simp [gradientStateIndex, stateGradient]
  rw [hi]
  exact (fderiv_axis_eq_deriv_update
    (solvedDarbouxQ_first_variables_differentiableAt g (statePoint w)
      (stateGradient w) (w 4) (w 5) hw.2) i).symm

theorem sixVariableQ_gradient_axis_expanded {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) (i : Fin 2) :
    fderiv ℝ (sixVariableQ g) w (Pi.single (gradientStateIndex i) 1) =
      christoffel g i 1 1 (statePoint w) -
        2 * (stateMixed g w / stateQDenominator g w) * christoffel g i 0 1 (statePoint w) +
        (stateMixed g w / stateQDenominator g w) ^ 2 * christoffel g i 0 0 (statePoint w) +
        gaussianCurvature g (statePoint w) *
          (coordPartial i (jetEnergy g (statePoint w)) (stateGradient w) / stateQDenominator g w +
            stateEnergy g w * christoffel g i 0 0 (statePoint w) / (stateQDenominator g w) ^ 2) := by
  rw [sixVariableQ_gradient_axis hg hU hw i]
  exact solvedDarbouxQ_firstJet_expanded g (statePoint w) (stateGradient w) (w 4) (w 5) hw.2 i

theorem sixVariableQ_mixed_axis {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    fderiv ℝ (sixVariableQ g) w (Pi.single 4 1) =
      2 * (stateMixed g w / stateQDenominator g w) := by
  have hd := ((sixVariableQ_contDiffOn hg hU).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hd]
  have heq : (fun t => sixVariableQ g (Function.update w 4 t)) =
      (fun t => solvedDarbouxQ g (statePoint w) t (w 5) (stateGradient w)) :=
    funext (sixVariableQ_update_mixed hg hU hw.1)
  rw [heq, solvedDarbouxQ_deriv_b g (statePoint w) (stateGradient w) (w 4) (w 5) hw.2]
  rfl

theorem sixVariableQ_xx_axis {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    fderiv ℝ (sixVariableQ g) w (Pi.single 5 1) =
      -((stateMixed g w / stateQDenominator g w) ^ 2 +
        gaussianCurvature g (statePoint w) * stateEnergy g w / (stateQDenominator g w) ^ 2) := by
  have hd := ((sixVariableQ_contDiffOn hg hU).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hd]
  have heq : (fun t => sixVariableQ g (Function.update w 5 t)) =
      (fun t => solvedDarbouxQ g (statePoint w) (w 4) t (stateGradient w)) :=
    funext (sixVariableQ_update_xx hg hU hw.1)
  rw [heq, solvedDarbouxQ_deriv_c g (statePoint w) (stateGradient w) (w 4) (w 5) hw.2]
  rfl

def qSolutionJet (z : Coord → ℝ) (p : Coord) : DarbouxState :=
  ![p 0, p 1, coordPartial 0 z p, coordPartial 1 z p,
    coordPartial 0 (coordPartial 1 z) p, coordPartial 0 (coordPartial 0 z) p]

theorem statePoint_qSolutionJet (z : Coord → ℝ) (p : Coord) :
    statePoint (qSolutionJet z p) = p := by
  ext i
  fin_cases i <;> rfl

theorem stateGradient_qSolutionJet (z : Coord → ℝ) (p : Coord) :
    stateGradient (qSolutionJet z p) = fun i => coordPartial i z p := by
  ext i
  fin_cases i <;> rfl

theorem stateQDenominator_qSolutionJet (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    stateQDenominator g (qSolutionJet z p) = covHessian g z p 0 0 := by
  unfold stateQDenominator
  rw [statePoint_qSolutionJet, stateGradient_qSolutionJet]
  exact jetXX_at_height g p z

theorem qToPState_qSolutionJet {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    qToPState (qSolutionJet z p) = solutionJet (swappedHeight z) (coordinateSwap p) := by
  have hp' : coordinateSwap (coordinateSwap p) ∈ U := by simpa using hp
  have hd : DifferentiableAt ℝ z (coordinateSwap (coordinateSwap p)) :=
    ((hz.contDiffAt (hU.mem_nhds hp')).differentiableAt (by simp))
  have hfirst (i : Fin 2) : coordPartial i (swappedHeight z) (coordinateSwap p) =
      coordPartial (swapCoordinateIndex i) z p := by
    simpa only [coordinateSwap_involutive] using coordPartial_swap_comp hd i
  have hsecond (i j : Fin 2) :
      coordPartial i (coordPartial j (swappedHeight z)) (coordinateSwap p) =
        coordPartial (swapCoordinateIndex i) (coordPartial (swapCoordinateIndex j) z) p := by
    simpa only [coordinateSwap_involutive] using second_coordPartial_swap_comp hz hU hp' i j
  ext i
  fin_cases i <;>
    simp [qToPState, qToPStateIndex, qSolutionJet, solutionJet, hfirst, hsecond,
      coordPartial_comm hz hU hp 1 0]

theorem qSolutionJet_mem_domain {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    qSolutionJet z p ∈ darbouxQStateDomain g U := by
  constructor
  · simpa only [statePoint_qSolutionJet] using hp
  · simpa only [stateQDenominator_qSolutionJet] using hxx

theorem darbouxDet_iff_sixVariableQ {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p ↔
      coordPartial 1 (coordPartial 1 z) p = sixVariableQ g (qSolutionJet z p) := by
  rw [sixVariableQ_explicit hg hU (by simpa only [statePoint_qSolutionJet] using hp),
    statePoint_qSolutionJet, stateGradient_qSolutionJet]
  exact darbouxDet_iff_solvedQ_at_height hg hU hz hp hxx

end SmoothLocal.HighEquation

end

end OAI
