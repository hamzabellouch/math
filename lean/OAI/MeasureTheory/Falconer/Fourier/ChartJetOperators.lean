import OAI.MeasureTheory.Falconer.Fourier.ParametricJets
import OAI.MeasureTheory.Falconer.Estimates.LaplacianIsometry
import OAI.MeasureTheory.Falconer.Fourier.StationaryTransport
import OAI.MeasureTheory.Falconer.Fourier.StationaryCoefficients

namespace OAI

/-!
# Actual stationary operators on a smooth pole patch

The operators are the quadratic Laplacian jets of the explicit chart
amplitude. They depend smoothly on the evaluation direction away from the
opposite pole. Their equality with the coefficients in the local
sphere expansion follows by locality, including the fixed chart cutoff.
-/

namespace Falconer
open Set Metric
open scoped ContDiff Topology

noncomputable def unmaskedStationaryAmplitude (m : ℕ) (B : Space (m+3) → ℂ)
    (z : Space (m+3) × Space (m+2)) : ℂ :=
  ((Real.sqrt (1-‖z.2‖^2/4))^m : ℂ) *
    B (poleRotationFormula (gnomonicChart (0 : Space (m+2))) z.1 (quadraticSpherePoint z.2))

theorem unmaskedStationaryAmplitude_contDiffAt (m : ℕ) {B : Space (m+3) → ℂ}
    (hB : ContDiff ℝ ∞ B) {e : Space (m+3)} {u : Space (m+2)}
    (he : (gnomonicChart (0 : Space (m+2)) : Space (m+3)) + e ≠ 0)
    (hu : ‖u‖ < 1) : ContDiffAt ℝ ∞ (unmaskedStationaryAmplitude m B) (e,u) := by
  have hu2 : ‖u‖^2 < 1 := by
    simpa using (sq_lt_sq₀ (norm_nonneg u) (by norm_num : (0:ℝ) ≤ 1)).mpr hu
  have hd : ContDiffAt ℝ ∞
      (fun v : Space (m+2) => ((Real.sqrt (1-‖v‖^2/4))^m : ℂ)) u := by
    apply ContDiffAt.pow
    exact Complex.ofRealCLM.contDiff.comp_contDiffAt u
      ((contDiffAt_const.sub ((contDiff_norm_sq ℝ).contDiffAt.div_const 4)).sqrt
        (by linarith : 1-‖u‖^2/4 ≠ 0))
  have hq := (quadraticSpherePoint_contDiffAt (hu.trans (by norm_num))).comp (e,u)
    contDiffAt_snd
  have hr := (poleRotationFormula_contDiffAt
    (gnomonicChart (0 : Space (m+2))) e (quadraticSpherePoint u) he).comp (e,u)
      (contDiffAt_fst.prodMk hq)
  exact (hd.comp (e,u) contDiffAt_snd).mul (hB.contDiffAt.comp (e,u) hr)

noncomputable def actualStationaryCoefficient (m j : ℕ) (B : Space (m+3) → ℂ)
    (e : Space (m+3)) : ℂ :=
  quadraticJetCoefficient j (fun u => unmaskedStationaryAmplitude m B (e,u))

theorem actualStationaryCoefficient_contDiffAt (m j : ℕ) {B : Space (m+3) → ℂ}
    (hB : ContDiff ℝ ∞ B) {e : Space (m+3)}
    (he : (gnomonicChart (0 : Space (m+2)) : Space (m+3)) + e ≠ 0) :
    ContDiffAt ℝ ∞ (actualStationaryCoefficient m j B) e := by
  exact quadraticJetCoefficient_contDiffAt
    (unmaskedStationaryAmplitude_contDiffAt m hB he (by simp)) j

theorem actualStationaryCoefficient_eq (m j : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) :
    actualStationaryCoefficient m j B e =
      quadraticJetCoefficient j (quadraticAmplitude m
        (fun w => B (sphereMap (stationaryPoleRotation e) w))) := by
  apply quadraticJetCoefficient_congr
  filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : Space (m+2)) ∈ ball 0 1)] with u hu
  have hu' : ‖u‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hu
  simp only [unmaskedStationaryAmplitude, quadraticAmplitude, indicator_of_mem hu]
  congr 1
  congr 1
  rw [← stationaryPoleRotation_apply, ← gnomonicChart_quadraticToGnomonic hu']
  rfl

@[simp] theorem actualStationaryCoefficient_zero (m : ℕ) (B : Space (m+3) → ℂ)
    (e : Sphere (m+3)) :
    actualStationaryCoefficient m 0 B e = sphereStationaryConstant (m+2) * B e := by
  rw [actualStationaryCoefficient_eq, quadraticJetCoefficient_amplitude_zero]
  change _ * B (stationaryPoleRotation e (gnomonicChart (0 : Space (m+2)))) = _
  rw [stationaryPoleRotation_pole]

/-- The actual coefficient depends only on the original amplitude near its
evaluation direction; every cutoff that is constant there is invisible. -/
theorem actualStationaryCoefficient_local (m j : ℕ) {B G : Space (m+3) → ℂ}
    (e : Sphere (m+3)) (hBG : B =ᶠ[𝓝 (e : Space (m+3))] G) :
    actualStationaryCoefficient m j B e = actualStationaryCoefficient m j G e := by
  apply quadraticJetCoefficient_congr
  let γ : Space (m+2) → Space (m+3) :=
    fun u => stationaryPoleRotation e (quadraticSpherePoint u)
  have hq0 : quadraticSpherePoint (0 : Space (m+2)) =
      (gnomonicChart (0 : Space (m+2)) : Space (m+3)) := by
    simpa [quadraticToGnomonic] using
      (gnomonicChart_quadraticToGnomonic (u := (0 : Space (m+2))) (by simp)).symm
  have hγ0 : γ 0 = (e : Space (m+3)) := by
    change stationaryPoleRotation e (quadraticSpherePoint 0) = _
    rw [hq0, stationaryPoleRotation_pole]
  have hγ : Filter.Tendsto γ (𝓝 (0 : Space (m+2))) (𝓝 (e : Space (m+3))) := by
    rw [← hγ0]
    exact (stationaryPoleRotation e).continuous.continuousAt.comp
      (quadraticSpherePoint_contDiffAt (u := (0 : Space (m+2))) (by simp)).continuousAt
  filter_upwards [hBG.comp_tendsto hγ] with u hu
  simp only [unmaskedStationaryAmplitude, ← stationaryPoleRotation_apply]
  rw [show B (stationaryPoleRotation e (quadraticSpherePoint u)) =
    G (stationaryPoleRotation e (quadraticSpherePoint u)) from hu]

end Falconer

end OAI
