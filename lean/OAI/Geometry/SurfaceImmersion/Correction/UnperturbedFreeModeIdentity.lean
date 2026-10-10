import OAI.Geometry.SurfaceImmersion.Geometry.UnperturbedSolverScale
import OAI.Geometry.SurfaceImmersion.Correction.ChartedCombinedMean

namespace OAI

/-! The unperturbed supported solver is exactly the explicit finite
metric-mode parametrix, including its quadratic mean. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial
variable {n : ℕ} {G : Field n} {U : Set Base}

lemma perturbedFreeMode_zero (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (V : SupportedField (F := Ambient n) K) (q : ℕ) :
    (perturbedFreeMode τ hG h K hKU 0 V q : Field n) = modeApprox τ G V (fun _ => 0) q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have he : (fun p => conjugatedD τ G
        (perturbedFreeMode τ hG h K hKU 0 V q) p) =
        residual τ G (fun _ => 0) (modeApprox τ G V (fun _ => 0) q) := by
      rw [ih]
      funext p
      simp only [residual, sub_zero]
    funext p
    change (perturbedFreeMode τ hG h K hKU 0 V q) p -
      initialAmplitude τ G (fun _ => 0)
        (fun y => conjugatedD τ G (perturbedFreeMode τ hG h K hKU 0 V q) y + 0 - 0) p = _
    simp only [add_zero, sub_zero, he]
    rw [show (perturbedFreeMode τ hG h K hKU 0 V q) p =
      modeApprox τ G V (fun _ => 0) q p from congrFun ih p]
    rfl

lemma perturbedFreeLM_zero (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (V : SupportedField (F := Ambient n) K) (q : ℕ) :
    (perturbedFreeLM τ hG h K hKU 0 q V : Field n) = modeApprox τ G V (fun _ => 0) q := by
  rw [perturbedFreeLM_apply]
  exact perturbedFreeMode_zero τ hG h K hKU V q

end ClosedSurfaceR4.SmallModes

namespace ClosedSurfaceR4.RealModes
open SmallModes
open JetPolynomial (SupportedField)
variable {F : RField 4} {U : Set Base}

lemma normalizedPerturbedMean_zero (δ τ : ℝ) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (q : ℕ) (b : SupportedField (F := ℝ) K) (v w p : Base) :
    normalizedPerturbedMean δ τ hF h K hKU 0 q b v w p =
      normalizedMeanError δ τ F b q v w p := by
  have he := perturbedFreeLM_zero τ (contDiff_complexify hF) (h.complexDomain hF)
    K hKU (supportedFreeSeed δ τ hF h K hKU b) q
  change δ⁻¹ ^ 2 *
    (QuadraticMean.zeroPair
      (gradientAmplitude τ (perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF)
        K hKU 0 q (supportedFreeSeed δ τ hF h K hKU b)) v p)
      (gradientAmplitude τ (perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF)
        K hKU 0 q (supportedFreeSeed δ τ hF h K hKU b)) w p) -
      QuadraticMean.zeroPair (leadingDerivative τ (freeSeed δ τ b F) v p)
        (leadingDerivative τ (freeSeed δ τ b F) w p)) = _
  rw [he]
  simp only [normalizedMeanError, modeMeanError, inv_pow]
  rfl

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P 0 G hG φ K τ s)

lemma operator_unperturbed : c.operator = 0 :=
  phaseChartPolynomialOperator_zero c.openO c.openU P c.smoothP hG c.mapsG K c.supportU
    c.smoothPhase τ c.e c.smoothForward c.smoothInverse c.supportChart

lemma metricMeanInChart_unperturbed (δ : ℝ) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) :
    c.metricMeanInChart δ q b = meanTensor δ τ c.realMap b q := by
  funext y k
  unfold metricMeanInChart
  rw [c.operator_unperturbed]
  exact normalizedPerturbedMean_zero δ τ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) q b (firstDirection k) (secondDirection k) y

lemma combinedMeanField_unperturbed (δ : ℝ) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) (x : SmallModes.Base) :
    c.combinedMeanField δ q b x = c.e.source.indicator
      (fun p => pullbackField c.e p (meanTensor δ τ c.realMap b q (c.e p))) x := by
  have hz : c.polynomialMeanField δ q b = 0 := by
    ext y k
    change normalizedPolynomialMean (P k) δ 0 G φ (c.originalFreeSeed δ q b) τ 0 y = 0
    simp [normalizedPolynomialMean, quadraticMeanCoefficient, conjugated]
  change c.metricMeanField δ q b x + (pushSupported planeCoordinateIsometry K (c.polynomialMeanField δ q b)) x = _
  rw [hz]
  change c.metricMeanField δ q b x + (0 : Tensor) = _
  rw [add_zero, metricMeanField_apply, c.metricMeanInChart_unperturbed]

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
