import OAI.Geometry.SurfaceImmersion.Atlas.FixedChartGeometry
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseDenominatorNeighborhood
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialNonlinearSolver

namespace OAI

/-! Actual nonlinear solvers on a fixed phase chart. Only its open domain is
restricted when the immersed map changes; all coordinate budgets stay fixed. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean RealModes PhaseGeometry

def fixedChartSolverBudget (J B : ℕ → ℝ) (D : ℝ) (m : ℕ) : ℝ :=
  1+B m+J (m+3)+2*(J 1)^2+2*D

lemma fixedChartSolverBudget_polynomial (J : ℕ → ℝ) (B : ℕ → ℝ → ℝ)
    {D : ℝ} (hJ : ∀ m, 0 ≤ J m) (hD : 0 ≤ D)
    (hB : ∀ m, HasPolynomialBound (B m)) (m : ℕ) :
    HasPolynomialBound (fun x => fixedChartSolverBudget J (fun j => B j x) D m) := by
  exact ((((polynomialBound_const zero_le_one).add (hB m)).add
    (polynomialBound_const (hJ (m+3)))).add
      (polynomialBound_const (mul_nonneg (by norm_num) (sq_nonneg (J 1))))).add
        (polynomialBound_const (mul_nonneg (by norm_num) hD))

theorem fixed_chart_nonlinear_solver :
    ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
    ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
      {φ : Base → ℝ} (_hφ : ContDiff ℝ ∞ φ)
      (e : NoncriticalPhaseChart (coordinatePhase φ)),
      (modeSupport K : Set SmallModes.Base) ⊆ e.chart.source →
      ∀ J : ℕ → ℝ, (∀ m, 1 ≤ J m) →
      (∀ m j, j ≤ m → ∀ x ∈ e.chart.source,
        ‖iteratedFDerivWithin ℝ j e.chart e.chart.source x‖ ≤ J m) →
      (∀ m j, j ≤ m → ∀ x ∈ e.chart.target,
        ‖iteratedFDerivWithin ℝ j e.chart.symm e.chart.target x‖ ≤ J m) →
      ∀ D : ℝ, 1 ≤ D →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        Function.Injective (fderiv ℝ (G ∘ planeCoordinateIsometry.symm) x)) →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        Good (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (phaseDerivative (coordinatePhase φ) x)) →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        ‖(NormalFrame.gramDet
          (SmallModes.coordDeriv SmallModes.dx (G ∘ planeCoordinateIsometry.symm) x)
          (SmallModes.coordDeriv SmallModes.dy (G ∘ planeCoordinateIsometry.symm) x))⁻¹‖ ≤ D) →
      (∀ x ∈ (modeSupport K : Set SmallModes.Base),
        ‖secondQuadratic (realSecondTensor (G ∘ planeCoordinateIsometry.symm) x)
          (-(phaseDerivative (coordinatePhase φ) x).2,
            (phaseDerivative (coordinatePhase φ) x).1)‖⁻¹ ≤ D) →
      ∀ (τ : ℝ) (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ B : ℕ → ℝ, (∀ m, 1 ≤ B m) →
      (∀ m j, j ≤ m+3 → WeightedBound e.chart.source 1 j
        (B m/(s : ℝ)^(j-2)) (G ∘ planeCoordinateIsometry.symm)) →
      ∃ c : PolynomialSolveData emptyMetricPolynomial 0 G hG φ K τ s,
        (∀ m, c.C m = A m*(fixedChartSolverBudget J B D m)^(p m)) ∧
        (∀ m, c.D m = 0) ∧ (∀ m, c.J m = fixedChartSolverBudget J B D m) ∧
        (∀ m j, j ≤ m → ∀ x ∈ c.e.target,
          ‖iteratedFDerivWithin ℝ j c.e.symm c.e.target x‖ ≤ J m) := by
  obtain ⟨p,A,hA,hsolve⟩ := polynomial_nonlinear_unperturbed_solver
  refine ⟨p,A,hA,?_⟩
  intro G hG K φ hφ e hKe J hJ hf hi D hD hImm hgood hgram hnormal τ s hs hs1 B hB hFj
  have hF := hG.comp planeCoordinateIsometry.symm.contDiff
  have hφ' := hφ.comp planeCoordinateIsometry.symm.contDiff
  obtain ⟨U,hU,hKU,hgeom⟩ := phase_denominator_neighborhood hF hφ' (modeSupport K)
    (zero_lt_one.trans_le hD) hImm hgood hgram hnormal
  let d := e.chart.restrOpen U hU
  have hd : ContDiff ℝ ∞ d := e.smooth
  have hdi : ContDiff ℝ ∞ d.symm := e.smoothInverse
  have hf' := restrict_chart_forward_jets e.chart U hU J hf
  have hi' := restrict_chart_inverse_jets e.chart U hU J hi
  have hdf (x : SmallModes.Base) (hx : x ∈ e.chart.source) :
      ‖fderiv ℝ e.chart x‖ ≤ J 1 := by
    have hh := hf 1 1 le_rfl x hx
    rwa [iteratedFDerivWithin_of_isOpen 1 e.chart.open_source hx,norm_iteratedFDeriv_one] at hh
  have hdb (x : SmallModes.Base) (hx : x ∈ e.chart.target) :
      ‖fderiv ℝ e.chart.symm x‖ ≤ J 1 := by
    have hh := hi 1 1 le_rfl x hx
    rwa [iteratedFDerivWithin_of_isOpen 1 e.chart.open_target hx,norm_iteratedFDeriv_one] at hh
  have hjac := chart_jacobian_bounds e.chart e.smooth e.smoothInverse
    (zero_le_one.trans (hJ 1)) hdf hdb
  let E := fixedChartSolverBudget J B D
  have heach (m : ℕ) : 1 ≤ E m ∧ B m ≤ E m ∧ J (m+3) ≤ E m ∧
      2*(J 1)^2 ≤ E m ∧ 2*D ≤ E m := by
    have hb0 := zero_le_one.trans (hB m)
    have hj0 := zero_le_one.trans (hJ (m+3))
    have hd0 := zero_le_one.trans hD
    have hs0 := sq_nonneg (J 1)
    dsimp [E,fixedChartSolverBudget]
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  obtain ⟨c,he,hC,hzero,hcj⟩ := hsolve hG K hφ d hd hdi e.phase
    (fun x hx => ⟨hKe hx,hKU hx⟩)
    (fun x hx => (hgeom x hx.2).1) (fun x hx => (hgeom x hx.2).2.1)
    τ s hs hs1 E (fun m => (heach m).1) (by
      intro m
      refine ⟨?_,?_,?_,?_,?_,?_⟩
      · intro j hj
        have hh : WeightedBound d.source 1 j (B m/(s : ℝ)^(j-2))
            (G ∘ planeCoordinateIsometry.symm) := by
          intro k hk x hx
          rw [iteratedFDerivWithin_of_isOpen k d.open_source hx]
          have hv := hFj m j hj k hk x hx.1
          rwa [iteratedFDerivWithin_of_isOpen k e.chart.open_source hx.1] at hv
        exact hh.mono_const (div_le_div_of_nonneg_right (heach m).2.1 (pow_nonneg hs.le _))
      · intro j _ hj x hx
        exact (hf' (m+3) j hj x hx).trans (heach m).2.2.1
      · intro x hx
        exact (hjac x hx.1).2.trans (heach m).2.2.2.1
      · intro x hx
        exact (hjac x hx.1).1.trans (heach m).2.2.2.1
      · intro x hx
        exact (hgeom x hx.2).2.2.1.trans (heach m).2.2.2.2
      · intro x hx
        exact (hgeom x hx.2).2.2.2.trans (heach m).2.2.2.2)
  refine ⟨c,hC,hzero,hcj,?_⟩
  intro m j hj x hx
  rw [he] at hx ⊢
  exact hi' m j hj x hx

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
