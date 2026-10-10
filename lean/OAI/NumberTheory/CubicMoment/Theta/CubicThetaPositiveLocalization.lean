import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAxisDifferentials
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! Products supported inside positive height extend continuously and
smoothly across the unused boundary, regardless of the other factor there. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPositiveProduct_continuous {φ f : ℂ × ℝ → ℂ}
    (hφ : Continuous φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (hf : ContinuousOn f {y : ℂ × ℝ | 0<y.2}) : Continuous (φ*f) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases h : 0<p.2
  · exact hφ.continuousAt.mul (hf.continuousAt ((isOpen_lt continuous_const continuous_snd).mem_nhds h))
  · have hout : p∉tsupport (φ*f) := fun hq => h (hp (tsupport_mul_subset_left hq))
    exact (continuousAt_const : ContinuousAt (fun _ : ℂ × ℝ => (0:ℂ)) p).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hout)

lemma cubicThetaPositiveProduct_integrable {φ f : ℂ × ℝ → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (hf : ContinuousOn f {y : ℂ × ℝ | 0<y.2}) : Integrable (φ*f) :=
  (cubicThetaPositiveProduct_continuous hφ hp hf).integrable_of_hasCompactSupport hc.mul_right

lemma cubicThetaPositiveProduct_contDiff {φ f : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hp : tsupport φ⊆{y : ℂ × ℝ | 0<y.2})
    (hf : ContDiffOn ℝ 1 f {y : ℂ × ℝ | 0<y.2}) : ContDiff ℝ 1 (φ*f) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases h : 0<p.2
  · exact (hφ.contDiffOn.mul hf).contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds h)
  · have hout : p∉tsupport (φ*f) := fun hq => h (hp (tsupport_mul_subset_left hq))
    exact (contDiffAt_const : ContDiffAt ℝ 1 (fun _ : ℂ × ℝ => (0:ℂ)) p).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hout)

lemma cubicThetaAxisFirst_continuous (k : CubicThetaAxis) {φ : ℂ × ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) : Continuous (cubicThetaAxisFirst k φ) := by
  have he : cubicThetaAxisFirst k φ=(fun p => fderiv ℝ φ p (cubicThetaAxisVector k)) :=
    funext (fun p => cubicThetaAxisFirst_eq_fderiv k φ (hφ.differentiable one_ne_zero p))
  rw [he]
  exact (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

lemma cubicThetaAxisFirst_support (k : CubicThetaAxis) (φ : ℂ × ℝ → ℂ) :
    tsupport (cubicThetaAxisFirst k φ)⊆tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro p hp
  by_contra hout
  apply hp
  have ht : φ=ᶠ[𝓝 p] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hout
  have hl : Tendsto (cubicThetaCoordinateLine k p.1.re p.1.im p.2)
      (𝓝 (cubicThetaCoordinateCenter k p.1.re p.1.im p.2)) (𝓝 p) := by
    have h : ContinuousAt (cubicThetaCoordinateLine k p.1.re p.1.im p.2)
        (cubicThetaCoordinateCenter k p.1.re p.1.im p.2) :=
      (cubicThetaCoordinateLine_continuous k p.1.re p.1.im p.2).continuousAt
    simpa only [ContinuousAt,cubicThetaCoordinateLine_center,cubicThetaCartesianPoint_self] using h
  have he := ht.comp_tendsto hl
  simp only [Function.comp_def] at he
  unfold cubicThetaAxisFirst
  simpa only [deriv_const] using he.deriv_eq

end CubicFirstMoment

end

end OAI
