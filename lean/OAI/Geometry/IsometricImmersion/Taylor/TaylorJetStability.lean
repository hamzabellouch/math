import OAI.Geometry.IsometricImmersion.Taylor.TaylorSeparatedProduct

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem secondCoordPartial_add {P R : Coord → ℝ} {V : Set Coord}
    (hV : IsOpen V) (hP : ContDiffOn ℝ ∞ P V) (hR : ContDiffOn ℝ ∞ R V)
    {p : Coord} (hp : p ∈ V) (i j : Fin 2) :
    coordPartial i (coordPartial j (fun q => P q + R q)) p =
      coordPartial i (coordPartial j P) p + coordPartial i (coordPartial j R) p := by
  have he : coordPartial j (fun q => P q + R q) =ᶠ[𝓝 p]
      (fun q => coordPartial j P q + coordPartial j R q) := by
    filter_upwards [hV.mem_nhds hp] with q hq
    exact HessianCalculus.coordPartial_add_at
      ((hP.contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp))
      ((hR.contDiffAt (hV.mem_nhds hq)).differentiableAt (by simp)) j
  rw [coordPartial_eq_of_eventuallyEq he i]
  exact HessianCalculus.coordPartial_add_at
    (((partial_contDiffOn hP hV j).contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp))
    (((partial_contDiffOn hR hV j).contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)) i

def correctionState (C : ℝ → ℝ) (a : ℝ) (n : ℕ) (p : Coord) : DarbouxState :=
  ![0, 0,
    deriv C (p 0) * normalizedTimePower a (n + 2) (p 1),
    C (p 0) * normalizedTimePower a (n + 1) (p 1),
    deriv C (p 0) * normalizedTimePower a (n + 1) (p 1),
    deriv (deriv C) (p 0) * normalizedTimePower a (n + 2) (p 1)]

theorem correctionState_slice_contDiff (C : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ) :
    ContDiff ℝ ∞ (fun t => correctionState C a n ![x, t]) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · change ContDiff ℝ ∞ (fun t => deriv C x * normalizedTimePower a (n + 2) t)
    exact contDiff_const.mul (normalizedTimePower_contDiff a (n + 2))
  · change ContDiff ℝ ∞ (fun t => C x * normalizedTimePower a (n + 1) t)
    exact contDiff_const.mul (normalizedTimePower_contDiff a (n + 1))
  · change ContDiff ℝ ∞ (fun t => deriv C x * normalizedTimePower a (n + 1) t)
    exact contDiff_const.mul (normalizedTimePower_contDiff a (n + 1))
  · change ContDiff ℝ ∞ (fun t => deriv (deriv C) x * normalizedTimePower a (n + 2) t)
    exact contDiff_const.mul (normalizedTimePower_contDiff a (n + 2))

theorem correctionState_time_jets_zero (C : ℝ → ℝ) (a : ℝ) (n : ℕ) (x : ℝ)
    (k : ℕ) (hk : k ≤ n) :
    iteratedDeriv k (fun t => correctionState C a n ![x, t]) a = 0 := by
  ext i
  rw [iteratedDeriv_state_eval (correctionState_slice_contDiff C a n x).contDiffAt k i]
  fin_cases i
  · exact iteratedDeriv_fun_const_zero
  · exact iteratedDeriv_fun_const_zero
  · change iteratedDeriv k (fun t => deriv C x * normalizedTimePower a (n + 2) t) a = 0
    rw [coefficient_timePower_jet, ite_eq_right (by omega)]
  · change iteratedDeriv k (fun t => C x * normalizedTimePower a (n + 1) t) a = 0
    rw [coefficient_timePower_jet, ite_eq_right (by omega)]
  · change iteratedDeriv k (fun t => deriv C x * normalizedTimePower a (n + 1) t) a = 0
    rw [coefficient_timePower_jet, ite_eq_right (by omega)]
  · change iteratedDeriv k (fun t => deriv (deriv C) x * normalizedTimePower a (n + 2) t) a = 0
    rw [coefficient_timePower_jet, ite_eq_right (by omega)]

theorem qSolutionJet_add_taylorCorrection {P : Coord → ℝ} {C : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    qSolutionJet (fun q => P q + taylorCorrection C a n q) p =
      qSolutionJet P p + correctionState C a n p := by
  have hV := spatialStrip_isOpen hI
  have hR := taylorCorrection_contDiffOn hC a n
  have hdP := (hP.contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
  have hdR := (hR.contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)
  ext i
  fin_cases i
  · exact (add_zero (p 0)).symm
  · exact (add_zero (p 1)).symm
  · change coordPartial 0 (fun q => P q + taylorCorrection C a n q) p = _
    rw [HessianCalculus.coordPartial_add_at hdP hdR 0,
      taylorCorrection_partial_x hC hI a n hp]
    rfl
  · change coordPartial 1 (fun q => P q + taylorCorrection C a n q) p = _
    rw [HessianCalculus.coordPartial_add_at hdP hdR 1,
      taylorCorrection_partial_t hC hI a n hp]
    rfl
  · change coordPartial 0 (coordPartial 1 (fun q => P q + taylorCorrection C a n q)) p = _
    rw [secondCoordPartial_add hV hP hR hp 0 1,
      taylorCorrection_partial_xt hC hI a n hp]
    rfl
  · change coordPartial 0 (coordPartial 0 (fun q => P q + taylorCorrection C a n q)) p = _
    rw [secondCoordPartial_add hV hP hR hp 0 0,
      taylorCorrection_partial_xx hC hI a n hp]
    rfl

theorem qSolutionJet_time_slice_contDiffAt {P : Coord → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    {x : ℝ} (hx : x ∈ I) (a : ℝ) :
    ContDiffAt ℝ ∞ (fun t => qSolutionJet P ![x, t]) a :=
  ((qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).contDiffAt
    ((spatialStrip_isOpen hI).mem_nhds hx)).comp a (verticalPoint_contDiff x).contDiffAt

theorem qSolutionJet_taylorCorrection_time_jets
    {P : Coord → ℝ} {C : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ I) :
    ∀ k ≤ n,
      iteratedDeriv k (fun t => qSolutionJet
        (fun q => P q + taylorCorrection C a n q) ![x, t]) a =
      iteratedDeriv k (fun t => qSolutionJet P ![x, t]) a := by
  have he : (fun t => qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, t]) =
      (fun t => qSolutionJet P ![x, t] + correctionState C a n ![x, t]) := by
    funext t
    exact qSolutionJet_add_taylorCorrection hI hP hC a n hx
  rw [he]
  exact iteratedDeriv_add_eq_of_zero_jets
    (qSolutionJet_time_slice_contDiffAt hI hP hx a)
    (correctionState_slice_contDiff C a n x).contDiffAt
    (fun k hk => correctionState_time_jets_zero C a n x k hk)

theorem sixVariableQ_taylorCorrection_time_jets
    {g : MetricField} {U : Set Coord} {P : Coord → ℝ} {C : ℝ → ℝ} {I : Set ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n : ℕ) {x : ℝ} (hx : x ∈ I)
    (hp : (![x, a] : Coord) ∈ U) (hxx : covHessian g P ![x, a] 0 0 ≠ 0) :
    ∀ k ≤ n,
      iteratedDeriv k (fun t => sixVariableQ g (qSolutionJet
        (fun q => P q + taylorCorrection C a n q) ![x, t])) a =
      iteratedDeriv k (fun t => sixVariableQ g (qSolutionJet P ![x, t])) a := by
  intro k hk
  have hnew := hP.add (taylorCorrection_contDiffOn hC a n)
  have hj := qSolutionJet_taylorCorrection_time_jets hI hP hC a n hx
  have hvalue : qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, a] =
      qSolutionJet P ![x, a] := by simpa only [iteratedDeriv_zero] using hj 0 (by omega)
  have hQ := sixVariableQ_contDiffAt_solutionJet hg hU hp hxx
  rw [← hvalue] at hQ
  exact iteratedDeriv_comp_eq_of_jets (Q := sixVariableQ g)
    (qSolutionJet_time_slice_contDiffAt hI hnew hx a)
    (qSolutionJet_time_slice_contDiffAt hI hP hx a) hQ
    (fun j hjk => hj j (hjk.trans hk))

end SmoothLocal.Taylor

end

end OAI
