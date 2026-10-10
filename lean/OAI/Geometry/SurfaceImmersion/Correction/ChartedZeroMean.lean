import OAI.Geometry.SurfaceImmersion.Correction.ChartedFreeSeed
import OAI.Geometry.Immersion.ClosedSurface.MeanBilinearity

namespace OAI

/-! The actual zero phase of a transported free amplitude. The metric
part transforms as a covariant tensor through the phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.RealModes
open SmallModes
open QuadraticMean (derivativeAmplitude)

lemma phaseZeroTensor_congr {n : ℕ} {φ ψ : Base → ℝ} {Z W : Field n} {p : Base}
    (hφ : φ =ᶠ[nhds p] ψ) (hZ : Z =ᶠ[nhds p] W) (τ : ℝ) :
    phaseZeroTensor τ φ Z p = phaseZeroTensor τ ψ W p := by
  unfold phaseZeroTensor derivativeAmplitude
  rw [Filter.EventuallyEq.fderiv_eq hφ, Filter.EventuallyEq.fderiv_eq hZ, hZ.eq_of_nhds]

lemma phaseZeroTensor_chart {n : ℕ}
    (e : OpenPartialHomeomorph Base Base) (he : ContDiffOn ℝ ∞ e e.source)
    (K : Compacts Base) (hK : (K : Set Base) ⊆ e.source)
    {φ : Base → ℝ} (hφ : ∀ x ∈ e.source, (e x).1 = φ x) (τ : ℝ)
    (Z : JetPolynomial.SupportedField (F := Ambient n) (JetPolynomial.chartSupport e K hK))
    {p : Base} (hp : p ∈ e.source) :
    phaseZeroTensor τ φ (JetPolynomial.chartPull e he K hK Z) p =
      PhaseMean.pullbackField e p (phaseZeroTensor τ Prod.fst Z (e p)) := by
  have hphase : φ =ᶠ[nhds p] (fun x => (e x).1) := by
    filter_upwards [e.open_source.mem_nhds hp] with x hx using (hφ x hx).symm
  have hseed : (JetPolynomial.chartPull e he K hK Z : Field n) =ᶠ[nhds p] Z ∘ e := by
    filter_upwards [e.open_source.mem_nhds hp] with x hx
    exact Set.indicator_of_mem hx _
  rw [phaseZeroTensor_congr hphase hseed τ]
  exact phaseZeroTensor_coordinate (Z.contDiff.differentiable (by simp) _)
    ((he.contDiffAt (e.open_source.mem_nhds hp)).differentiableAt (by simp)) τ

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes
open SmallModes (gradientAmplitude)
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

def metricMeanInChart (δ : ℝ) (q : ℕ) (b : SupportedField (F := ℝ) c.chartCompact) :
    SmallModes.Base → Tensor := fun y k =>
  normalizedPerturbedMean δ τ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) c.operator q b
    (firstDirection k) (secondDirection k) y

def leadingInChart (b : SupportedField (F := ℝ) c.chartCompact) : SmallModes.Base → Tensor :=
  fun y k => b y ^ 2 * (firstDirection k).1 * (secondDirection k).1

lemma freeSeed_zeroPhase {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) {y : SmallModes.Base} (hy : y ∈ c.e.target) :
    phaseZeroTensor τ Prod.fst (c.freeSeed δ q b) y =
      δ ^ 2 • (c.leadingInChart b y + c.metricMeanInChart δ q b y) := by
  funext k
  simp only [phaseZeroTensor, ← SmallModes.gradientAmplitude_eq, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
  exact perturbed_seed_mean_identity δ τ hδ hτ c.smoothMap c.realDomain c.chartCompact
    (chartSupport_subset c.e (modeSupport K) c.supportChart) c.operator q b
    (firstDirection k) (secondDirection k) y hy

lemma originalFreeSeed_zeroPhase {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (b : SupportedField (F := ℝ) c.chartCompact) {x : SmallModes.Base} (hx : x ∈ c.e.source) :
    phaseZeroTensor τ (coordinatePhase φ) (coordinateAmplitude (c.originalFreeSeed δ q b)) x =
      δ ^ 2 • (pullbackField c.e x (c.leadingInChart b (c.e x)) +
        pullbackField c.e x (c.metricMeanInChart δ q b (c.e x))) := by
  have he : coordinateAmplitude (c.originalFreeSeed δ q b) =
      (chartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.freeSeed δ q b) : SmallModes.Field 4) := by
    funext y
    change (chartPull c.e c.smoothForward (modeSupport K) c.supportChart (c.freeSeed δ q b))
      (planeCoordinateIsometry (planeCoordinateIsometry.symm y)) = _
    rw [planeCoordinateIsometry.apply_symm_apply]
  rw [he, phaseZeroTensor_chart c.e c.smoothForward (modeSupport K) c.supportChart c.phase τ _ hx,
    c.freeSeed_zeroPhase hδ hτ q b (c.e.map_source hx), map_smul, map_add]

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
