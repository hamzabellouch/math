import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailIntegral

namespace OAI

/-! The absolutely convergent backward tail integral acts on bounded continuous sources. -/

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExteriorTailIntegral_continuous (κ C : ℝ) (hκ : 0 < κ)
    (g : ℝ → ℂ × ℂ) (hg : Continuous g) (hbound : ∀ s, ‖g s‖ ≤ C) :
    Continuous (radialExteriorTailIntegral κ g) := by
  unfold radialExteriorTailIntegral
  apply Continuous.neg
  apply continuous_of_dominated
    (bound := fun u : ℝ => Real.exp (-κ*u)*C)
  · intro t
    apply Continuous.aestronglyMeasurable
    unfold radialExteriorPropagator radialExteriorPhase
    fun_prop
  · intro t
    exact Eventually.of_forall (fun u => by
      change ‖Real.exp (-κ*u) • radialExteriorPropagator t (t+u) (g (t+u))‖ ≤ Real.exp (-κ*u)*C
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),radialExteriorPropagator_norm]
      exact mul_le_mul_of_nonneg_left (hbound _) (Real.exp_nonneg _))
  · exact (exp_neg_integrableOn_Ioi 0 hκ).mul_const C
  · apply Eventually.of_forall
    intro u
    unfold radialExteriorPropagator radialExteriorPhase
    fun_prop

noncomputable def boundedRadialExteriorTail (κ : ℝ) (hκ : 0 < κ)
    (g : ℝ →ᵇ ℂ × ℂ) : ℝ →ᵇ ℂ × ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (radialExteriorTailIntegral κ g)
    (radialExteriorTailIntegral_continuous κ ‖g‖ hκ g g.continuous g.norm_coe_le_norm)
    (‖g‖/κ) (radialExteriorTailIntegral_norm κ ‖g‖ · hκ g g.continuous g.norm_coe_le_norm)

theorem boundedRadialExteriorTail_norm (κ : ℝ) (hκ : 0 < κ) (g : ℝ →ᵇ ℂ × ℂ) :
    ‖boundedRadialExteriorTail κ hκ g‖ ≤ ‖g‖/κ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro t
  exact radialExteriorTailIntegral_norm κ ‖g‖ t hκ g g.continuous g.norm_coe_le_norm

theorem radialExteriorTailIntegral_sub (κ : ℝ) (hκ : 0 < κ)
    (g h : ℝ →ᵇ ℂ × ℂ) (t : ℝ) :
    radialExteriorTailIntegral κ (g-h) t=
      radialExteriorTailIntegral κ g t-radialExteriorTailIntegral κ h t := by
  unfold radialExteriorTailIntegral
  have hiG := radialExteriorTailIntegral_integrable κ ‖g‖ t hκ g g.continuous g.norm_coe_le_norm
  have hiH := radialExteriorTailIntegral_integrable κ ‖h‖ t hκ h h.continuous h.norm_coe_le_norm
  change -(∫ u in Ioi (0 : ℝ), Real.exp (-κ*u) •
    radialExteriorPropagator t (t+u) (g (t+u)-h (t+u))) = _
  simp only [radialExteriorPropagator_sub,smul_sub]
  rw [integral_sub hiG hiH]
  abel

theorem boundedRadialExteriorTail_difference (κ : ℝ) (hκ : 0 < κ)
    (g h : ℝ →ᵇ ℂ × ℂ) :
    ‖boundedRadialExteriorTail κ hκ g-boundedRadialExteriorTail κ hκ h‖ ≤ ‖g-h‖/κ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro t
  change ‖radialExteriorTailIntegral κ g t-radialExteriorTailIntegral κ h t‖ ≤ _
  rw [← radialExteriorTailIntegral_sub κ hκ g h t]
  exact radialExteriorTailIntegral_norm κ ‖g-h‖ t hκ (g-h) (g-h).continuous (g-h).norm_coe_le_norm

end DefocusingNLS

end OAI
