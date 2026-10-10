import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFOverlap

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cdfDistance_symm (α γ : ℝ → ℝ) : cdfDistance α γ=cdfDistance γ α := by
  unfold cdfDistance
  simp only [abs_sub_comm]

theorem cdfDistance_triangle {α γ η : ℝ → ℝ} (hα : Monotone α) (hγ : Monotone γ) (hη : Monotone η) :
    cdfDistance α η≤cdfDistance α γ+cdfDistance γ η := by
  unfold cdfDistance
  rw [← integral_add (cdfDistance_integrable hα hγ) (cdfDistance_integrable hγ hη)]
  exact integral_mono (cdfDistance_integrable hα hη)
    ((cdfDistance_integrable hα hγ).add (cdfDistance_integrable hγ hη)) (fun _ => abs_sub_le _ _ _)

theorem cdfDistance_difference {α γ α' γ' : ℝ → ℝ}
    (hα : Monotone α) (hγ : Monotone γ) (ha : Monotone α') (hg : Monotone γ') :
    |cdfDistance α' γ'-cdfDistance α γ|≤cdfDistance α' α+cdfDistance γ' γ := by
  apply abs_le.mpr
  have H₁ := cdfDistance_triangle ha hα hγ
  have H₂ := cdfDistance_triangle ha hg hγ
  have H₃ := cdfDistance_triangle hα ha hg
  have H₄ := cdfDistance_triangle ha hγ hg
  rw [cdfDistance_symm α α'] at H₃
  rw [cdfDistance_symm γ γ'] at H₄
  have H₅ := cdfDistance_triangle hα hg hγ
  have H₆ := cdfDistance_triangle ha hα hg
  have H₇ := cdfDistance_triangle hα ha hγ
  constructor
  · linarith
  · linarith

theorem cdfDistance_tendsto {α γ : ℝ → ℝ} {αn γn : ℕ → ℝ → ℝ}
    (hα : Monotone α) (hγ : Monotone γ) (ha : ∀ n, Monotone (αn n)) (hg : ∀ n, Monotone (γn n))
    (hA : Tendsto (fun n => cdfDistance (αn n) α) atTop (𝓝 0))
    (hB : Tendsto (fun n => cdfDistance (γn n) γ) atTop (𝓝 0)) :
    Tendsto (fun n => cdfDistance (αn n) (γn n)) atTop (𝓝 (cdfDistance α γ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero (fun _ => abs_nonneg _)
    (fun n => cdfDistance_difference hα hγ (ha n) (hg n)) (by simpa using hA.add hB)

theorem unitInterval_abs_integral_le {f : ℝ → ℝ} {C : ℝ}
    (hC : ∀ x∈Icc (0:ℝ) 1, |f x|≤C) : |∫ x in Icc (0:ℝ) 1, f x|≤C := by
  have H := norm_setIntegral_le_of_norm_le_const_ae (μ:=volume) (f:=f)
    (s:=Icc (0:ℝ) 1) (C:=C) (by simp)
    ((ae_restrict_mem measurableSet_Icc).mono (fun x hx => by simpa only [Real.norm_eq_abs] using hC x hx))
  simpa only [Real.norm_eq_abs,Real.volume_real_Icc,sub_zero,max_eq_left zero_le_one,mul_one] using H

theorem unitInterval_tendsto_integral_uniform {f : ℝ → ℝ} {fn : ℕ → ℝ → ℝ}
    (hf : IntegrableOn f (Icc (0:ℝ) 1)) (hfn : ∀ n, IntegrableOn (fn n) (Icc (0:ℝ) 1))
    (hu : TendstoUniformlyOn fn f atTop (Icc (0:ℝ) 1)) :
    Tendsto (fun n => ∫ x in Icc (0:ℝ) 1, fn n x) atTop (𝓝 (∫ x in Icc (0:ℝ) 1, f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have H := Metric.tendstoUniformlyOn_iff.mp hu (ε/2) (by positivity)
  filter_upwards [H] with n hn
  rw [Real.dist_eq,← integral_sub (hfn n) hf]
  exact (unitInterval_abs_integral_le (fun x hx => by
    simpa only [Real.dist_eq,abs_sub_comm] using (hn x hx).le)).trans_lt (by linarith)

end SK.Analytic

end
end

end OAI
