import OAI.Geometry.IsometricImmersion.Calculus.VerticalSliceJets
import OAI.Geometry.IsometricImmersion.Darboux.ActualDriftEquation
import Mathlib.Analysis.Calculus.Deriv.Pi

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem fderiv_axis_eq_deriv_update {n : ℕ} {f : (Fin n → ℝ) → ℝ} {w : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f w) (i : Fin n) :
    fderiv ℝ f w (Pi.single i 1) = deriv (fun t => f (Function.update w i t)) (w i) := by
  have hd : HasFDerivAt f (fderiv ℝ f w) (Function.update w i (w i)) := by
    simpa using hf.hasFDerivAt
  exact (hd.comp_hasDerivAt (w i) (hasDerivAt_update w i (w i))).deriv.symm

def gradientStateIndex (i : Fin 2) : Fin 6 := if i = 0 then 2 else 3

theorem sixVariableP_update_gradient (g : MetricField) (w : DarbouxState) (i : Fin 2) (t : ℝ) :
    sixVariableP g (Function.update w (gradientStateIndex i) t) =
      solvedDarboux g (statePoint w) (w 4) (w 5) (Function.update (stateGradient w) i t) := by
  have hp : statePoint (Function.update w (gradientStateIndex i) t) = statePoint w := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [gradientStateIndex, statePoint]
  have hv : stateGradient (Function.update w (gradientStateIndex i) t) =
      Function.update (stateGradient w) i t := by
    ext j
    fin_cases i <;> fin_cases j <;> simp [gradientStateIndex, stateGradient]
  unfold sixVariableP
  rw [hp, hv]
  fin_cases i <;> simp [gradientStateIndex]

theorem sixVariableP_update_mixed (g : MetricField) (w : DarbouxState) (t : ℝ) :
    sixVariableP g (Function.update w 4 t) =
      solvedDarboux g (statePoint w) t (w 5) (stateGradient w) := by
  have hp : statePoint (Function.update w 4 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 4 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  unfold sixVariableP
  rw [hp, hv]
  simp

theorem sixVariableP_update_yy (g : MetricField) (w : DarbouxState) (t : ℝ) :
    sixVariableP g (Function.update w 5 t) =
      solvedDarboux g (statePoint w) (w 4) t (stateGradient w) := by
  have hp : statePoint (Function.update w 5 t) = statePoint w := by
    ext j
    fin_cases j <;> simp [statePoint]
  have hv : stateGradient (Function.update w 5 t) = stateGradient w := by
    ext j
    fin_cases j <;> simp [stateGradient]
  unfold sixVariableP
  rw [hp, hv]
  simp

theorem solvedDarboux_first_variables_differentiableAt (g : MetricField) (p u : Coord) (b c : ℝ)
    (hyy : jetYY g p c u ≠ 0) : DifferentiableAt ℝ (solvedDarboux g p b c) u := by
  have hd := (jetConnection_differentiableAt g p u 0 0).add
    ((jetNumerator_differentiableAt g p u b).mul ((jetYY_differentiableAt g p u c).inv hyy))
  exact hd

theorem sixVariableP_gradient_axis
    {g : MetricField} {U : Set Coord} {w : DarbouxState}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hw : w ∈ darbouxStateDomain g U) (i : Fin 2) :
    fderiv ℝ (sixVariableP g) w (Pi.single (gradientStateIndex i) 1) =
      coordPartial i (solvedDarboux g (statePoint w) (w 4) (w 5)) (stateGradient w) := by
  have hP : DifferentiableAt ℝ (sixVariableP g) w :=
    ((sixVariableP_contDiffOn hg hU).contDiffAt
      ((darbouxStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hP]
  have heq : (fun t => sixVariableP g (Function.update w (gradientStateIndex i) t)) =
      (fun t => solvedDarboux g (statePoint w) (w 4) (w 5) (Function.update (stateGradient w) i t)) :=
    funext (sixVariableP_update_gradient g w i)
  rw [heq]
  have hi : w (gradientStateIndex i) = stateGradient w i := by
    fin_cases i <;> simp [gradientStateIndex, stateGradient]
  rw [hi]
  exact (fderiv_axis_eq_deriv_update
    (solvedDarboux_first_variables_differentiableAt g (statePoint w) (stateGradient w) (w 4) (w 5) hw.2) i).symm

theorem sixVariableP_gradient_axis_at_height
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single (gradientStateIndex i) 1) =
      heightPFirst g z i p := by
  rw [sixVariableP_gradient_axis hg hU (solutionJet_mem_domain g z hp hyy) i,
    statePoint_solutionJet, stateGradient_solutionJet]
  rfl

theorem sixVariableP_mixed_axis_at_height
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 4 1) = 2 * hessianQuotient g z p := by
  have hP := (sixVariableP_contDiffAt_solutionJet hg hU hp hyy).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hP]
  have heq : (fun t => sixVariableP g (Function.update (solutionJet z p) 4 t)) =
      (fun t => solvedDarboux g p t (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p)) := by
    funext t
    rw [sixVariableP_update_mixed, statePoint_solutionJet, stateGradient_solutionJet]
    rfl
  rw [heq]
  change deriv (fun t => solvedDarboux g p t (coordPartial 1 (coordPartial 1 z) p)
    (fun i => coordPartial i z p)) (coordPartial 0 (coordPartial 1 z) p) = _
  rw [solvedDarboux_deriv_b g p _ _ _ hyy, jetMixed_at_height, jetYY_at_height]
  rfl

theorem sixVariableP_yy_axis_at_height
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 5 1) =
      -((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) := by
  have hP := (sixVariableP_contDiffAt_solutionJet hg hU hp hyy).differentiableAt (by simp)
  rw [fderiv_axis_eq_deriv_update hP]
  have heq : (fun t => sixVariableP g (Function.update (solutionJet z p) 5 t)) =
      (fun t => solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p) t (fun i => coordPartial i z p)) := by
    funext t
    rw [sixVariableP_update_yy, statePoint_solutionJet, stateGradient_solutionJet]
    rfl
  rw [heq]
  change deriv (fun t => solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p) t
    (fun i => coordPartial i z p)) (coordPartial 1 (coordPartial 1 z) p) = _
  rw [solvedDarboux_deriv_c g p _ _ _ hyy, jetMixed_at_height, jetYY_at_height,
    jetEnergy_at_height hg hp z]
  unfold hessianQuotient darbouxG
  ring

theorem sixVariableP_vertical_direction
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (v : DarbouxState) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) v =
      heightPFirst g z 0 p * v 2 + heightPFirst g z 1 p * v 3 +
        2 * hessianQuotient g z p * v 4 -
        ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) * v 5 := by
  have he : v = v 2 • (Pi.single 2 (1 : ℝ) : DarbouxState) +
      v 3 • Pi.single 3 1 + v 4 • Pi.single 4 1 + v 5 • Pi.single 5 1 := by
    ext i
    fin_cases i <;> simp [hv0, hv1]
  have h0 : fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 2 1) = heightPFirst g z 0 p := by
    simpa only [gradientStateIndex, ↓reduceIte] using sixVariableP_gradient_axis_at_height hg hU hp hyy 0
  have h1 : fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 3 1) = heightPFirst g z 1 p := by
    simpa only [gradientStateIndex, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] using
      sixVariableP_gradient_axis_at_height hg hU hp hyy 1
  have hl := congrArg (fderiv ℝ (sixVariableP g) (solutionJet z p)) he
  simp only [map_add, map_smul, h0, h1, sixVariableP_mixed_axis_at_height hg hU hp hyy,
    sixVariableP_yy_axis_at_height hg hU hp hyy, smul_eq_mul] at hl
  rw [hl]
  ring

end SmoothLocal.HighEquation

end

end OAI
