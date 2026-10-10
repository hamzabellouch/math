import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorPropagator
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Topology.ContinuousMap.Bounded.Normed

namespace OAI

/-! Absolute convergence and the exact weighted bound for the backward tail integral. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def radialExteriorTailIntegral (κ : ℝ) (g : ℝ → ℂ × ℂ) (t : ℝ) : ℂ × ℂ :=
  -∫ u in Ioi (0 : ℝ), Real.exp (-κ*u) • radialExteriorPropagator t (t+u) (g (t+u))

theorem radialExteriorTailIntegral_integrable (κ C t : ℝ) (hκ : 0 < κ)
    (g : ℝ → ℂ × ℂ) (hg : Continuous g) (hbound : ∀ s, ‖g s‖ ≤ C) :
    IntegrableOn (fun u => Real.exp (-κ*u) • radialExteriorPropagator t (t+u) (g (t+u)))
      (Ioi (0 : ℝ)) := by
  have hc : Continuous (fun u => Real.exp (-κ*u) • radialExteriorPropagator t (t+u) (g (t+u))) := by
    unfold radialExteriorPropagator radialExteriorPhase
    fun_prop
  apply ((exp_neg_integrableOn_Ioi 0 hκ).mul_const C).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun u => by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),radialExteriorPropagator_norm]
    exact mul_le_mul_of_nonneg_left (hbound _) (Real.exp_nonneg _))

theorem radialExteriorTailIntegral_norm (κ C t : ℝ) (hκ : 0 < κ)
    (g : ℝ → ℂ × ℂ) (hg : Continuous g) (hbound : ∀ s, ‖g s‖ ≤ C) :
    ‖radialExteriorTailIntegral κ g t‖ ≤ C/κ := by
  have hi := radialExteriorTailIntegral_integrable κ C t hκ g hg hbound
  unfold radialExteriorTailIntegral
  rw [norm_neg]
  calc
    _ ≤ ∫ u in Ioi (0 : ℝ), ‖Real.exp (-κ*u) • radialExteriorPropagator t (t+u) (g (t+u))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-κ*u)*C := by
      apply integral_mono_ae hi.norm ((exp_neg_integrableOn_Ioi 0 hκ).mul_const C)
      exact Filter.Eventually.of_forall (fun u => by
        change ‖Real.exp (-κ*u) • radialExteriorPropagator t (t+u) (g (t+u))‖ ≤ Real.exp (-κ*u)*C
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),radialExteriorPropagator_norm]
        exact mul_le_mul_of_nonneg_left (hbound _) (Real.exp_nonneg _))
    _ = C/κ := by
      rw [integral_mul_const,integral_exp_mul_Ioi (neg_lt_zero.mpr hκ)]
      simp
      ring

end DefocusingNLS

end OAI
