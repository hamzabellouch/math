import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartRealization

namespace OAI

/-! The exact full conjugated linear operator in a local phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes

lemma realOsc_add_value {n : ℕ} (τ : ℝ) (Z W : SmallModes.Field n) (p : SmallModes.Base) :
    realOsc τ (Z + W) p = realOsc τ Z p + realOsc τ W p := by
  ext k
  simp [realOsc, SmallModes.oscillate, QuadraticMean.realPart, mul_add]

lemma realLinearized_conjugated_value {n : ℕ} {F : RField n} {Z : SmallModes.Field n}
    {p : SmallModes.Base} (hF : DifferentiableAt ℝ F p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) :
    realLinearizedTensor F (realOsc τ Z) p =
      realOsc τ (SmallModes.conjugatedD τ (fun q => complexify (F q)) Z) p := by
  have hr := realLinearized_residual hF hZ τ (0 : SmallModes.Tensor)
  have hz : realOsc τ (0 : SmallModes.Tensor) p = 0 := by
    ext k
    simp [realOsc, SmallModes.oscillate, QuadraticMean.realPart]
  rw [hz, sub_zero] at hr
  have he : SmallModes.residual τ (fun q => complexify (F q)) 0 Z =
      SmallModes.conjugatedD τ (fun q => complexify (F q)) Z := by
    funext q
    simp only [SmallModes.residual, Pi.zero_apply, sub_zero]
  rwa [he] at hr

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean
variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

theorem phaseChartFullLinearization
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
    let F := (G ∘ planeCoordinateIsometry.symm) ∘ e.symm
    let R := phaseChartPolynomialOperator hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe
    pullbackField e.symm y (coordinateFullLinearized P ε G X (e.symm y)) =
      RealModes.realOsc τ (SmallModes.conjugatedD τ (fun p => RealModes.complexify (F p)) Z + (R Z : SmallModes.Tensor)) y := by
  dsimp only
  change pullbackField e.symm y
    (RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) _ (e.symm y) +
      coordinateRealLinearized P ε G _ 0 (e.symm y)) = _
  rw [map_add, chart_metric_linearized e he hi (modeSupport K) hKe
    (hG.comp planeCoordinateIsometry.symm.contDiff)
    (hφ.comp planeCoordinateIsometry.symm.contDiff) hphase τ Z hy,
    phaseChartPolynomialOperator_realization hO hU P hP hG hQ K hKU hφ τ ε e he hi hKe hphase Z hy]
  have hF : DifferentiableAt ℝ ((G ∘ planeCoordinateIsometry.symm) ∘ e.symm) y :=
    ((hG.comp planeCoordinateIsometry.symm.contDiff).differentiable (by simp) _).comp y
      ((hi.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp))
  rw [RealModes.realLinearized_conjugated_value hF (Z.contDiff.differentiable (by simp) y) τ,
    RealModes.realOsc_add_value]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
