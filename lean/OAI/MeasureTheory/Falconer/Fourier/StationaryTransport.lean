import OAI.MeasureTheory.Falconer.Fourier.QuadraticStationary
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

namespace OAI

/-!
# Transport of the fixed-pole stationary expansion

A concrete orthogonal reflection takes the chart pole to any requested
unit direction. Rotation invariance transports the actual spherical
integral. Complex conjugation handles the opposite oscillatory sign.
Neither transport uses an additional published input.
-/

namespace Falconer
open MeasureTheory
open scoped RealInnerProductSpace ContDiff

noncomputable def stationaryPoleRotation {n : ℕ} (e : Sphere (n+1)) :
    Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) :=
  (ℝ ∙ ((gnomonicChart (0 : Space n) : Space (n+1)) + (e : Space (n+1)))).reflection

theorem stationaryPoleRotation_pole {n : ℕ} (e : Sphere (n+1)) :
    stationaryPoleRotation e (gnomonicChart (0 : Space n)) = (e : Space (n+1)) := by
  have h := Submodule.reflection_sub
    (v := (gnomonicChart (0 : Space n) : Space (n+1))) (w := -(e : Space (n+1)))
    (by rw [norm_neg, sphere_norm, sphere_norm])
  rw [sub_neg_eq_add, Submodule.reflection_orthogonal_apply] at h
  exact neg_injective h

/-- This formula gives smooth dependence on the requested pole whenever the
pole is separated from the antipode of `p`. -/
noncomputable def poleRotationFormula {n : ℕ} (p e x : Space n) : Space n :=
  (2 * inner ℝ (p+e) x / ‖p+e‖^2) • (p+e) - x

theorem stationaryPoleRotation_apply {n : ℕ} (e : Sphere (n+1)) (x : Space (n+1)) :
    stationaryPoleRotation e x =
      poleRotationFormula (gnomonicChart (0 : Space n)) e x := by
  rw [stationaryPoleRotation, Submodule.reflection_singleton_apply]
  simp [poleRotationFormula, two_smul, two_mul, add_div, add_smul]

theorem poleRotationFormula_contDiffAt {n : ℕ} (p e x : Space n) (he : p+e ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : Space n × Space n => poleRotationFormula p z.1 z.2) (e,x) := by
  have hv : ContDiffAt ℝ ∞ (fun z : Space n × Space n => p+z.1) (e,x) :=
    contDiffAt_const.add contDiffAt_fst
  have hx : ContDiffAt ℝ ∞ (fun z : Space n × Space n => z.2) (e,x) := contDiffAt_snd
  have hi := hv.inner ℝ hx
  have hn : ContDiffAt ℝ ∞ (fun z : Space n × Space n => ‖p+z.1‖^2) (e,x) :=
    (contDiff_norm_sq ℝ).contDiffAt.comp (e,x) hv
  exact ((contDiffAt_const.mul hi).div hn
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr he))).smul hv |>.sub hx

theorem stationaryPoleRotation_denominator {n : ℕ} (e : Sphere (n+1)) :
    ‖(gnomonicChart (0 : Space n) : Space (n+1)) + (e : Space (n+1))‖^2 =
      2 + 2 * inner ℝ (gnomonicChart (0 : Space n) : Space (n+1)) (e : Space (n+1)) := by
  rw [norm_add_sq_real, sphere_norm, sphere_norm]
  ring

noncomputable def sphereOscillation {d : ℕ} (Λ : ℝ) (e : Sphere d)
    (b : Sphere d → ℂ) : ℂ :=
  ∫ w : Sphere d, Complex.exp (Complex.I*(Λ : ℂ)*
    (inner ℝ (w : Space d) (e : Space d) : ℂ)) * b w ∂sphereMeasure d

theorem gnomonicChart_zero_pole (n : ℕ) :
    (gnomonicChart (0 : Space n) : Space (n+1)) = coordinateJoin (0 : Space n) 1 := by
  have hn : ‖northLift (0 : Space n)‖ = 1 := by
    have h : ‖northLift (0 : Space n)‖^2 = 1 := by
      simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using
        northLift_norm_sq (0 : Space n)
    nlinarith [norm_nonneg (northLift (0 : Space n))]
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [gnomonicChart_zero, hn]
    simp [coordinateJoin_eq]
  · simp [gnomonicChart_succ, coordinateJoin_eq]

theorem sphereOscillation_rotate (m : ℕ) (Λ : ℝ) (e : Sphere (m+3))
    (b : Sphere (m+3) → ℂ) :
    sphereOscillation Λ e b = quadraticSphereOscillation m Λ
      (fun w => b (sphereMap (stationaryPoleRotation e) w)) := by
  let T := stationaryPoleRotation e
  rw [sphereOscillation, ← sphere_integral_rotation T]
  unfold quadraticSphereOscillation
  apply integral_congr_ae
  filter_upwards with w
  have hp : (e : Space (m+3)) = T (gnomonicChart (0 : Space (m+2))) :=
    (stationaryPoleRotation_pole e).symm
  have hi : inner ℝ (sphereMap T w : Space (m+3)) (e : Space (m+3)) =
      inner ℝ (w : Space (m+3)) (coordinateJoin (0 : Space (m+2)) 1) := by
    change inner ℝ (T (w : Space (m+3))) (e : Space (m+3)) = _
    rw [hp, T.inner_map_map, gnomonicChart_zero_pole]
  rw [hi]

theorem sphereOscillation_neg {d : ℕ} (Λ : ℝ) (e : Sphere d) (b : Sphere d → ℂ) :
    sphereOscillation (-Λ) e b =
      star (sphereOscillation Λ e (fun w => star (b w))) := by
  rw [sphereOscillation, sphereOscillation]
  simp only [← starRingEnd_apply]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with w
  simp only [map_mul, Complex.conj_conj, ← Complex.exp_conj,
    Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  congr 2
  ring

end Falconer

end OAI
