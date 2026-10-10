import OAI.Geometry.IsometricImmersion.Taylor.TaylorJetStability

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

def qResidual (g : MetricField) (P : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 1 (coordPartial 1 P) p - sixVariableQ g (qSolutionJet P p)

def comparisonDomain (g : MetricField) (U : Set Coord) (P : Coord → ℝ)
    (I : Set ℝ) : Set Coord :=
  spatialStrip I ∩ qSolutionJet P ⁻¹' darbouxQStateDomain g U

theorem comparisonDomain_isOpen {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) :
    IsOpen (comparisonDomain g U P I) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  exact inter_mem ((spatialStrip_isOpen hI).mem_nhds hp.1)
    (((qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).contDiffAt
      ((spatialStrip_isOpen hI).mem_nhds hp.1)).continuousAt.preimage_mem_nhds
        ((darbouxQStateDomain_isOpen hg hU).mem_nhds hp.2))

theorem mem_comparisonDomain {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} {p : Coord}
    (hpI : p ∈ spatialStrip I) (hpU : p ∈ U) (hxx : covHessian g P p 0 0 ≠ 0) :
    p ∈ comparisonDomain g U P I :=
  ⟨hpI, qSolutionJet_mem_domain hpU hxx⟩

theorem comparisonDomain_denominator {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} {p : Coord}
    (hp : p ∈ comparisonDomain g U P I) :
    p ∈ U ∧ covHessian g P p 0 0 ≠ 0 := by
  exact ⟨by simpa only [statePoint_qSolutionJet] using hp.2.1,
    by simpa only [stateQDenominator_qSolutionJet] using hp.2.2⟩

theorem qResidual_contDiffOn {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) :
    ContDiffOn ℝ ∞ (qResidual g P) (comparisonDomain g U P I) := by
  have hs := spatialStrip_isOpen hI
  exact ((partial_contDiffOn (partial_contDiffOn hP hs 1) hs 1).mono
    (fun _ hp => hp.1)).sub
      ((sixVariableQ_contDiffOn hg hU).comp
        ((qSolutionJet_contDiffOn hs hP).mono (fun _ hp => hp.1)) (fun _ hp => hp.2))

theorem initialPoint_contDiff (a : ℝ) :
    ContDiff ℝ ∞ (fun x => (![x, a] : Coord)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const

def nextTaylorCoefficient (g : MetricField) (a : ℝ) (P : Coord → ℝ)
    (n : ℕ) (x : ℝ) : ℝ :=
  -verticalJet (qResidual g P) n ![x, a]

theorem nextTaylorCoefficient_contDiffOn {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) (a : ℝ) (n : ℕ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ I, covHessian g P ![x, a] 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (nextTaylorCoefficient g a P n) I :=
  ((verticalJet_contDiffOn (comparisonDomain_isOpen hg hU hI hP)
    (qResidual_contDiffOn hg hU hI hP) n).comp (initialPoint_contDiff a).contDiffOn
      (fun x hx => mem_comparisonDomain hx (hcut x hx) (hxx x hx))).neg

theorem nextTaylorCoefficient_eq_residual_jet {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) (a : ℝ) (n : ℕ)
    {x : ℝ} (hx : x ∈ I) (hp : (![x, a] : Coord) ∈ U)
    (hxx : covHessian g P ![x, a] 0 0 ≠ 0) :
    nextTaylorCoefficient g a P n x =
      -iteratedDeriv n (fun t => qResidual g P ![x, t]) a := by
  exact congrArg Neg.neg (verticalJet_slice (comparisonDomain_isOpen hg hU hI hP)
    (qResidual_contDiffOn hg hU hI hP) x n a (mem_comparisonDomain hx hp hxx)).symm

theorem qResidual_taylorCorrection_time_jet
    {g : MetricField} {U : Set Coord} {P : Coord → ℝ} {C : ℝ → ℝ} {I : Set ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n k : ℕ) (hk : k ≤ n)
    {x : ℝ} (hx : x ∈ I) (hp : (![x, a] : Coord) ∈ U)
    (hxx : covHessian g P ![x, a] 0 0 ≠ 0) :
    iteratedDeriv k (fun t => qResidual g
      (fun q => P q + taylorCorrection C a n q) ![x, t]) a =
      iteratedDeriv k (fun t => qResidual g P ![x, t]) a +
        if k = n then C x else 0 := by
  have hV := spatialStrip_isOpen hI
  have hR := taylorCorrection_contDiffOn hC a n
  have hnew := hP.add hR
  have htt : ContDiffAt ℝ ∞ (fun t => coordPartial 1 (coordPartial 1 P) ![x, t]) a :=
    ((partial_contDiffOn (partial_contDiffOn hP hV 1) hV 1).contDiffAt
      (hV.mem_nhds hx)).comp a (verticalPoint_contDiff x).contDiffAt
  have httnew : ContDiffAt ℝ ∞ (fun t => coordPartial 1 (coordPartial 1
      (fun q => P q + taylorCorrection C a n q)) ![x, t]) a :=
    ((partial_contDiffOn (partial_contDiffOn hnew hV 1) hV 1).contDiffAt
      (hV.mem_nhds hx)).comp a (verticalPoint_contDiff x).contDiffAt
  have hQouter := sixVariableQ_contDiffAt_solutionJet hg hU hp hxx
  have hQ : ContDiffAt ℝ ∞ (fun t => sixVariableQ g (qSolutionJet P ![x, t])) a :=
    ContDiffAt.comp (g := sixVariableQ g) (f := fun t => qSolutionJet P ![x, t])
      a hQouter (qSolutionJet_time_slice_contDiffAt hI hP hx a)
  have hstate : qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, a] =
      qSolutionJet P ![x, a] := by
    simpa only [iteratedDeriv_zero] using
      qSolutionJet_taylorCorrection_time_jets hI hP hC a n hx 0 (Nat.zero_le n)
  have hQouterNew : ContDiffAt ℝ ∞ (sixVariableQ g)
      (qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, a]) := by
    rw [hstate]
    exact hQouter
  have hQnew : ContDiffAt ℝ ∞ (fun t => sixVariableQ g
      (qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, t])) a :=
    ContDiffAt.comp (g := sixVariableQ g)
      (f := fun t => qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, t])
      a hQouterNew (qSolutionJet_time_slice_contDiffAt hI hnew hx a)
  have he : (fun t => coordPartial 1 (coordPartial 1
      (fun q => P q + taylorCorrection C a n q)) ![x, t]) =
      (fun t => coordPartial 1 (coordPartial 1 P) ![x, t] +
        C x * normalizedTimePower a n t) := by
    funext t
    rw [secondCoordPartial_add hV hP hR (p := ![x, t]) hx 1 1,
      taylorCorrection_partial_tt hC hI a n (p := ![x, t]) hx]
    rfl
  have hmon : ContDiffAt ℝ ∞ (fun t => C x * normalizedTimePower a n t) a :=
    (contDiff_const.mul (normalizedTimePower_contDiff a n)).contDiffAt
  change iteratedDeriv k (fun t =>
    coordPartial 1 (coordPartial 1 (fun q => P q + taylorCorrection C a n q)) ![x, t] -
      sixVariableQ g (qSolutionJet (fun q => P q + taylorCorrection C a n q) ![x, t])) a =
    iteratedDeriv k (fun t => coordPartial 1 (coordPartial 1 P) ![x, t] -
      sixVariableQ g (qSolutionJet P ![x, t])) a + _
  rw [iteratedDeriv_fun_sub (httnew.of_le (WithTop.coe_le_coe.mpr le_top))
      (hQnew.of_le (WithTop.coe_le_coe.mpr le_top)),
    iteratedDeriv_fun_sub (htt.of_le (WithTop.coe_le_coe.mpr le_top))
      (hQ.of_le (WithTop.coe_le_coe.mpr le_top)),
    sixVariableQ_taylorCorrection_time_jets hg hU hI hP hC a n hx hp hxx k hk,
    he, iteratedDeriv_fun_add (htt.of_le (WithTop.coe_le_coe.mpr le_top))
      (hmon.of_le (WithTop.coe_le_coe.mpr le_top)), coefficient_timePower_jet]
  ring

theorem nextTaylorCoefficient_cancels
    {g : MetricField} {U : Set Coord} {P : Coord → ℝ} {I : Set ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) (a : ℝ) (n : ℕ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ I, covHessian g P ![x, a] 0 0 ≠ 0)
    (hzero : ∀ x ∈ I, ∀ k < n, iteratedDeriv k (fun t => qResidual g P ![x, t]) a = 0) :
    ∀ x ∈ I, ∀ k < n + 1,
      iteratedDeriv k (fun t => qResidual g
        (fun q => P q + taylorCorrection (nextTaylorCoefficient g a P n) a n q) ![x, t]) a = 0 := by
  intro x hx k hk
  rw [qResidual_taylorCorrection_time_jet hg hU hI hP
    (nextTaylorCoefficient_contDiffOn hg hU hI hP a n hcut hxx)
    a n k (by omega) hx (hcut x hx) (hxx x hx)]
  by_cases hkn : k = n
  · subst k
    rw [ite_eq_left rfl, nextTaylorCoefficient_eq_residual_jet hg hU hI hP a n
      hx (hcut x hx) (hxx x hx)]
    ring
  · rw [ite_eq_right hkn, hzero x hx k (by omega), zero_add]

end SmoothLocal.Taylor

end

end OAI
