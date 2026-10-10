import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalSobolev
import OAI.Geometry.PrescribedRicci.KahlerCofactorDivergence

namespace OAI

/-! Complex Integration By Parts. -/

noncomputable section
open Matrix Filter Set Topology MeasureTheory
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
namespace KaehlerMetric
variable {d : ℕ}

def barDeriv (f : Coordinates d → ℂ) (z : Coordinates d) (j : Fin d) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ f z (coordinateVector j) +
    Complex.I * fderiv ℝ f z (Complex.I • coordinateVector j))

def holDeriv (f : Coordinates d → ℂ) (z : Coordinates d) (j : Fin d) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ f z (coordinateVector j) -
    Complex.I * fderiv ℝ f z (Complex.I • coordinateVector j))

lemma contDiff_deriv_direction {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ ∞ f) (v : E) : ContDiff ℝ ∞ (fun z => fderiv ℝ f z v) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma contDiff_barDeriv {f : Coordinates d → ℂ} (hf : ContDiff ℝ ∞ f) (j : Fin d) :
    ContDiff ℝ ∞ (fun z => barDeriv f z j) :=
  contDiff_const.mul ((contDiff_deriv_direction hf _).add
    (contDiff_const.mul (contDiff_deriv_direction hf _)))

lemma contDiff_holDeriv {f : Coordinates d → ℂ} (hf : ContDiff ℝ ∞ f) (j : Fin d) :
    ContDiff ℝ ∞ (fun z => holDeriv f z j) :=
  contDiff_const.mul ((contDiff_deriv_direction hf _).sub
    (contDiff_const.mul (contDiff_deriv_direction hf _)))

lemma compactSupport_barDeriv {f : Coordinates d → ℂ} (hf : HasCompactSupport f)
    (j : Fin d) : HasCompactSupport (fun z => barDeriv f z j) := by
  exact ((hf.fderiv_apply ℝ (coordinateVector j)).add
    (hf.fderiv_apply ℝ (Complex.I • coordinateVector j)).mul_left).mul_left

lemma integrable_mul_deriv {f g : Coordinates d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport f)
    (v : Coordinates d) : Integrable (fun z => f z * fderiv ℝ g z v) :=
  (hf.continuous.mul (contDiff_deriv_direction hg v).continuous).integrable_of_hasCompactSupport
    hc.mul_right

lemma integrable_deriv_mul {f g : Coordinates d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport f)
    (v : Coordinates d) : Integrable (fun z => fderiv ℝ f z v * g z) :=
  ((contDiff_deriv_direction hf v).continuous.mul hg.continuous).integrable_of_hasCompactSupport
    (hc.fderiv_apply ℝ v).mul_right

lemma contDiffAt_deriv_direction {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {z : E}
    (hf : ContDiffAt ℝ ∞ f z) (v : E) : ContDiffAt ℝ ∞ (fun y => fderiv ℝ f y v) z :=
  (hf.fderiv_right (by simp)).clm_apply contDiffAt_const

lemma continuous_mul_on_tsupport {E : Type*} [TopologicalSpace E] {f g : E → ℂ}
    (hf : Continuous f) (hg : ∀ z ∈ tsupport f, ContinuousAt g z) :
    Continuous (fun z => f z * g z) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ tsupport f
  · exact hf.continuousAt.mul (hg z hz)
  · apply (continuousAt_const (y := (0 : ℂ))).congr
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
    simp only [hy, zero_mul, Pi.zero_apply]

lemma contDiff_mul_on_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hg : ∀ z ∈ tsupport f, ContDiffAt ℝ ∞ g z) :
    ContDiff ℝ ∞ (fun z => f z * g z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport f
  · exact hf.contDiffAt.mul (hg z hz)
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
    simp only [hy, zero_mul, Pi.zero_apply]

lemma integrable_mul_deriv_local {f g : Coordinates d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ∀ z ∈ tsupport f, ContDiffAt ℝ ∞ g z)
    (hc : HasCompactSupport f) (v : Coordinates d) :
    Integrable (fun z => f z * fderiv ℝ g z v) :=
  (continuous_mul_on_tsupport hf.continuous (fun z hz =>
    (contDiffAt_deriv_direction (hg z hz) v).continuousAt)).integrable_of_hasCompactSupport
      hc.mul_right

lemma integrable_deriv_mul_local {f g : Coordinates d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ∀ z ∈ tsupport f, ContDiffAt ℝ ∞ g z)
    (hc : HasCompactSupport f) (v : Coordinates d) :
    Integrable (fun z => fderiv ℝ f z v * g z) :=
  (continuous_mul_on_tsupport (contDiff_deriv_direction hf v).continuous (fun z hz =>
    (hg z (tsupport_fderiv_apply_subset ℝ v hz)).continuousAt)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_right

lemma integral_mul_barDeriv_local {f g : Coordinates d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ∀ z ∈ tsupport f, ContDiffAt ℝ ∞ g z)
    (hc : HasCompactSupport f) (j : Fin d) :
    (∫ z, f z * barDeriv g z j) = -(∫ z, barDeriv f z j * g z) := by
  have hv (v : Coordinates d) : (∫ z, f z * fderiv ℝ g z v) =
      -(∫ z, fderiv ℝ f z v * g z) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (integrable_deriv_mul_local hf hg hc v) (integrable_mul_deriv_local hf hg hc v)
      ((continuous_mul_on_tsupport hf.continuous (fun z hz => (hg z hz).continuousAt)).integrable_of_hasCompactSupport hc.mul_right)
      (fun z _ => hf.differentiable (by simp) z)
      (fun z hz => (hg z hz).differentiableAt (by simp))
  have he (z : Coordinates d) : f z * barDeriv g z j =
      (2 : ℂ)⁻¹ * (f z * fderiv ℝ g z (coordinateVector j)) +
      ((2 : ℂ)⁻¹ * Complex.I) * (f z * fderiv ℝ g z (Complex.I • coordinateVector j)) := by
    unfold barDeriv
    ring
  have he' (z : Coordinates d) : barDeriv f z j * g z =
      (2 : ℂ)⁻¹ * (fderiv ℝ f z (coordinateVector j) * g z) +
      ((2 : ℂ)⁻¹ * Complex.I) * (fderiv ℝ f z (Complex.I • coordinateVector j) * g z) := by
    unfold barDeriv
    ring
  simp_rw [he, he']
  rw [integral_add ((integrable_mul_deriv_local hf hg hc _).const_mul _) ((integrable_mul_deriv_local hf hg hc _).const_mul _),
    integral_add ((integrable_deriv_mul_local hf hg hc _).const_mul _) ((integrable_deriv_mul_local hf hg hc _).const_mul _)]
  simp only [integral_const_mul, hv]
  ring

end KaehlerMetric
end Anticanonical.SourceSmooth

end

end OAI
