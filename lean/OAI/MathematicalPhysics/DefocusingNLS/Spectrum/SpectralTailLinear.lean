import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularTail

namespace OAI

/-! The backward circular integral is a bounded complex-linear operator. -/

open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem boundedRadialExteriorTail_zero (κ : ℝ) (hκ : 0 < κ) :
    boundedRadialExteriorTail κ hκ 0=0 := by
  apply BoundedContinuousFunction.ext
  intro t
  change radialExteriorTailIntegral κ (0 : ℝ →ᵇ ℂ × ℂ) t=0
  simp [radialExteriorTailIntegral,radialExteriorPropagator]

theorem boundedRadialExteriorTail_smul (κ : ℝ) (hκ : 0 < κ)
    (a : ℂ) (g : ℝ →ᵇ ℂ × ℂ) :
    boundedRadialExteriorTail κ hκ (a • g)=a • boundedRadialExteriorTail κ hκ g := by
  apply BoundedContinuousFunction.ext
  intro t
  change radialExteriorTailIntegral κ (a • g) t=a • radialExteriorTailIntegral κ g t
  have hp (u : ℝ) : radialExteriorPropagator t (t+u) ((a • g) (t+u))=
      a • radialExteriorPropagator t (t+u) (g (t+u)) := by
    apply Prod.ext <;> simp [radialExteriorPropagator,smul_eq_mul,mul_left_comm]
  unfold radialExteriorTailIntegral
  change -(∫ u in Ioi (0 : ℝ), Real.exp (-κ*u) •
    radialExteriorPropagator t (t+u) ((a • g) (t+u))) =
      a • -(∫ u in Ioi (0 : ℝ), Real.exp (-κ*u) •
        radialExteriorPropagator t (t+u) (g (t+u)))
  simp_rw [hp,smul_comm (Real.exp (-κ * _)) a]
  rw [integral_smul,smul_neg]

theorem boundedRadialExteriorTail_add (κ : ℝ) (hκ : 0 < κ)
    (g h : ℝ →ᵇ ℂ × ℂ) :
    boundedRadialExteriorTail κ hκ (g+h)=
      boundedRadialExteriorTail κ hκ g+boundedRadialExteriorTail κ hκ h := by
  have hs : boundedRadialExteriorTail κ hκ (-h)= -boundedRadialExteriorTail κ hκ h := by
    have he : boundedRadialExteriorTail κ hκ (0-h)=
        boundedRadialExteriorTail κ hκ 0-boundedRadialExteriorTail κ hκ h := by
      apply BoundedContinuousFunction.ext
      intro t
      exact radialExteriorTailIntegral_sub κ hκ 0 h t
    simpa only [zero_sub,boundedRadialExteriorTail_zero] using he
  have he : boundedRadialExteriorTail κ hκ (g-(-h))=
      boundedRadialExteriorTail κ hκ g-boundedRadialExteriorTail κ hκ (-h) := by
      apply BoundedContinuousFunction.ext
      intro t
      exact radialExteriorTailIntegral_sub κ hκ g (-h) t
  simpa only [sub_neg_eq_add,hs] using he

noncomputable def boundedRadialExteriorTailCLM (κ : ℝ) (hκ : 0 < κ) :
    (ℝ →ᵇ ℂ × ℂ) →L[ℂ] (ℝ →ᵇ ℂ × ℂ) :=
  LinearMap.mkContinuous
    { toFun := boundedRadialExteriorTail κ hκ
      map_add' := boundedRadialExteriorTail_add κ hκ
      map_smul' := fun a g => boundedRadialExteriorTail_smul κ hκ a g }
    (1/κ) (fun g => by
      change ‖boundedRadialExteriorTail κ hκ g‖ ≤ (1/κ)*‖g‖
      rw [one_div_mul_eq_div]
      exact boundedRadialExteriorTail_norm κ hκ g)

theorem circularTail_add (κ : ℝ) (hκ : 0 < κ) (g h : CircularTailSpace) :
    circularTail κ hκ (g+h)=circularTail κ hκ g+circularTail κ hκ h := by
  apply Prod.ext
  · exact boundedRadialExteriorTail_add κ hκ g.1 h.1
  · change star (boundedRadialExteriorTail κ hκ (star (g.2+h.2)))=_
    rw [star_add,boundedRadialExteriorTail_add,star_add]
    rfl

theorem circularTail_smul (κ : ℝ) (hκ : 0 < κ) (a : ℂ) (g : CircularTailSpace) :
    circularTail κ hκ (a • g)=a • circularTail κ hκ g := by
  apply Prod.ext
  · exact boundedRadialExteriorTail_smul κ hκ a g.1
  · change star (boundedRadialExteriorTail κ hκ (star (a • g.2)))=_
    rw [star_smul,boundedRadialExteriorTail_smul,star_smul,star_star]
    rfl

noncomputable def circularTailCLM (κ : ℝ) (hκ : 0 < κ) :
    CircularTailSpace →L[ℂ] CircularTailSpace :=
  LinearMap.mkContinuous
    { toFun := circularTail κ hκ
      map_add' := circularTail_add κ hκ
      map_smul' := fun a g => circularTail_smul κ hκ a g }
    (1/κ) (fun g => by
      change ‖circularTail κ hκ g‖ ≤ (1/κ)*‖g‖
      rw [one_div_mul_eq_div]
      exact circularTail_norm κ hκ g)

theorem circularTailCLM_norm (κ : ℝ) (hκ : 0 < κ) :
    ‖circularTailCLM κ hκ‖ ≤ 1/κ := by
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

end DefocusingNLS

end OAI
