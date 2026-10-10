import OAI.Geometry.SurfaceImmersion.Correction.ArbitraryPhasePolynomial

namespace OAI

/-! Actual local-coordinate realization of the polynomial phase operator.
The operator is transported, so no transformed-polynomial assumption is used. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

lemma chart_displacement_pull (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (K : Compacts SmallModes.Base)
    (hK : (K : Set SmallModes.Base) ⊆ e.source) (φ : SmallModes.Base → ℝ)
    (hphase : ∀ x ∈ e.source, (e x).1 = φ x) (τ : ℝ)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK))
    {y : SmallModes.Base} (hy : y ∈ e.target) :
    QuadraticMean.displacement τ φ (chartPull e he K hK Z) (e.symm y) =
      RealModes.realOsc τ Z y := by
  rw [RealModes.realOsc_eq_displacement]
  have hp := hphase (e.symm y) (e.map_target hy)
  rw [e.right_inv hy] at hp
  have hz : chartPull e he K hK Z (e.symm y) = Z y := by
    rw [chartPull_apply, Set.indicator_of_mem (e.map_target hy)]
    simp only [Function.comp_apply, e.right_inv hy]
  simp only [QuadraticMean.displacement, ← hp, hz]

def phaseChartPolynomialOperator (hO : IsOpen O) (hU : IsOpen U)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs O)
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε : ℝ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source) :
    SupportedField (F := Fin 4 → ℂ) (chartSupport e (modeSupport K) hKe) →ₗ[ℝ]
      SupportedField (F := ComplexTensor) (chartSupport e (modeSupport K) hKe) :=
  chartTensorTransportLM e (modeSupport K) hKe he hi
    (phaseCoordinatePolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε)

lemma phaseChartPolynomialOperator_realization
    (hO : IsOpen O) (hU : IsOpen U) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k l, (P k l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε : ℝ)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hKe : (modeSupport K : Set SmallModes.Base) ⊆ e.source)
    (hphase : ∀ x ∈ e.source, (e x).1 = coordinatePhase φ x)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e (modeSupport K) hKe))
    {y : SmallModes.Base} (hy : y ∈ e.target) :
    let X := QuadraticMean.displacement τ (coordinatePhase φ) (chartPull e he (modeSupport K) hKe Z)
    pullbackField e.symm y (coordinateRealLinearized P ε G X 0 (e.symm y)) =
      RealModes.realOsc τ (phaseChartPolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe Z) y := by
  dsimp only
  rw [phaseCoordinatePolynomialOperator_realization hO hU P hP hG hQ K hKU hφ τ ε]
  have hp := hphase (e.symm y) (e.map_target hy)
  rw [e.right_inv hy] at hp
  rw [RealModes.realOsc_eq_displacement]
  change pullbackField e.symm y (QuadraticMean.realMode (coordinatePhase φ (e.symm y) / τ)
      ((phaseCoordinatePolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε)
        (chartPull e he (modeSupport K) hKe Z) (e.symm y))) =
    QuadraticMean.realMode (y.1 / τ)
      (tensorChartPush e hi (modeSupport K) hKe
        ((phaseCoordinatePolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε)
          (chartPull e he (modeSupport K) hKe Z)) y)
  rw [tensorChartPush_apply, Set.indicator_of_mem hy, ← hp]
  exact (realMode_complexPullback (fderiv ℝ e.symm y) _ _).symm

lemma chart_metric_linearized (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)
    {F : RealModes.RField 4} (hF : ContDiff ℝ ∞ F) {φ : SmallModes.Base → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hphase : ∀ x ∈ e.source, (e x).1 = φ x) (τ : ℝ)
    (Z : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK))
    {y : SmallModes.Base} (hy : y ∈ e.target) :
    let X := QuadraticMean.displacement τ φ (chartPull e he K hK Z)
    pullbackField e.symm y (RealModes.realLinearizedTensor F X (e.symm y)) =
      RealModes.realLinearizedTensor (F ∘ e.symm) (RealModes.realOsc τ Z) y := by
  let X := QuadraticMean.displacement τ φ (chartPull e he K hK Z)
  have hX : ContDiff ℝ ∞ X := contDiffOn_univ.mp
    (RealModes.contDiffOn_displacement hφ.contDiffOn (chartPull e he K hK Z).contDiff.contDiffOn τ)
  have hid : X ∘ e.symm =ᶠ[nhds y] RealModes.realOsc τ Z := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact chart_displacement_pull e he K hK φ hphase τ Z hz
  have hc := RealModes.realLinearizedTensor_comp (hF.differentiable (by simp) _)
    (hX.differentiable (by simp) _) ((hi.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp))
  exact hc.symm.trans (RealModes.realLinearizedTensor_congr_right hid)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
