import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailOperator
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTailCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! Factoring the diagonal propagator out of the convergent backward integral. -/

open Set Filter MeasureTheory
namespace DefocusingNLS

noncomputable def radialExteriorPropagatorMap (t s : ℝ) : (ℂ × ℂ) →L[ℝ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℝ ℂ ℂ).prod
    (radialExteriorPhase t s • ContinuousLinearMap.snd ℝ ℂ ℂ)

@[simp] theorem radialExteriorPropagatorMap_apply (t s : ℝ) (v : ℂ × ℂ) :
    radialExteriorPropagatorMap t s v=radialExteriorPropagator t s v := rfl

noncomputable def radialExteriorGauge (κ : ℝ) (g : ℝ → ℂ × ℂ) (s : ℝ) : ℂ × ℂ :=
  Real.exp (-κ*s) • radialExteriorPropagator 0 s (g s)

theorem radialExteriorGauge_continuous (κ : ℝ) (g : ℝ → ℂ × ℂ) (hg : Continuous g) :
    Continuous (radialExteriorGauge κ g) := by
  unfold radialExteriorGauge radialExteriorPropagator radialExteriorPhase
  fun_prop

theorem radialExteriorGauge_integrable (κ C a : ℝ) (hκ : 0 < κ)
    (g : ℝ → ℂ × ℂ) (hg : Continuous g) (hbound : ∀ s, ‖g s‖ ≤ C) :
    IntegrableOn (radialExteriorGauge κ g) (Ioi a) := by
  apply ((exp_neg_integrableOn_Ioi a hκ).mul_const C).mono'
    (radialExteriorGauge_continuous κ g hg).aestronglyMeasurable
  exact Eventually.of_forall (fun s => by
    simp only [radialExteriorGauge,norm_smul,Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),radialExteriorPropagator_norm]
    exact mul_le_mul_of_nonneg_left (hbound s) (Real.exp_nonneg _))

theorem radialExteriorTailIntegral_representation (κ C t : ℝ) (hκ : 0 < κ)
    (g : ℝ → ℂ × ℂ) (hg : Continuous g) (hbound : ∀ s, ‖g s‖ ≤ C) :
    radialExteriorTailIntegral κ g t = -Real.exp (κ*t) •
      radialExteriorPropagator t 0 (∫ s in Ioi t, radialExteriorGauge κ g s) := by
  have hi := radialExteriorGauge_integrable κ C t hκ g hg hbound
  have he (u : ℝ) :
      Real.exp (-κ*u) • radialExteriorPropagator t (t+u) (g (t+u)) =
      Real.exp (κ*t) • radialExteriorPropagatorMap t 0 (radialExteriorGauge κ g (t+u)) := by
    simp only [radialExteriorGauge,ContinuousLinearMap.map_smul,
      radialExteriorPropagatorMap_apply,radialExteriorPropagator_comp,smul_smul]
    rw [← Real.exp_add]
    congr 2
    ring
  unfold radialExteriorTailIntegral
  simp_rw [he]
  rw [integral_smul,radial_tail_translate (fun s =>
    radialExteriorPropagatorMap t 0 (radialExteriorGauge κ g s)) t,
    (radialExteriorPropagatorMap t 0).integral_comp_comm hi]
  simp only [radialExteriorPropagatorMap_apply,neg_smul]

end DefocusingNLS

end OAI
