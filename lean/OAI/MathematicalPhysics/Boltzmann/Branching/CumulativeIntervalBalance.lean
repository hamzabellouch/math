import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakTimeLocalization
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

section

/-! # A finite source measure and its weak time primitive -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

def cumulative (μ : Measure ℝ) (t : ℝ) : ℝ := μ.real (Iic t)

theorem cumulative_monotone (μ : Measure ℝ) [IsFiniteMeasure μ] : Monotone (cumulative μ) := by
  intro s t hst
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.mpr hst))

theorem cumulative_locallyIntegrable (μ : Measure ℝ) [IsFiniteMeasure μ] :
    LocallyIntegrable (cumulative μ) := (cumulative_monotone μ).locallyIntegrable

theorem cumulative_weak_derivative (μ : Measure ℝ) [IsFiniteMeasure μ]
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (∫ t, deriv φ t*cumulative μ t) = -(∫ t, φ t ∂μ) := by
  let F : ℝ × ℝ → ℝ := {z : ℝ × ℝ | z.1 ≤ z.2}.indicator (fun z => deriv φ z.2)
  have hi : Integrable (deriv φ) (volume : Measure ℝ) :=
    (hφ.continuous_deriv (by simp)).integrable_of_hasCompactSupport hc.deriv
  have hF : Integrable F (μ.prod volume) :=
    (hi.comp_snd μ).indicator (measurableSet_le measurable_fst measurable_snd)
  have hright (t : ℝ) : (∫ s, F (s,t) ∂μ) = deriv φ t*cumulative μ t := by
    change (∫ s, (Iic t).indicator (fun _ => deriv φ t) s ∂μ) = _
    rw [integral_indicator measurableSet_Iic,integral_const]
    simp only [Measure.real,Measure.restrict_apply MeasurableSet.univ,univ_inter,
      smul_eq_mul,cumulative]
    exact mul_comm _ _
  have hleft (s : ℝ) : (∫ t, F (s,t)) = -φ s := by
    change (∫ t, (Ici s).indicator (deriv φ) t) = _
    rw [integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi]
    exact hc.integral_Ioi_deriv_eq (hφ.of_le (by simp)) s
  calc
    _ = ∫ t, ∫ s, F (s,t) ∂μ ∂volume := by simp only [hright]
    _ = ∫ s, ∫ t, F (s,t) ∂volume ∂μ :=
      (integral_integral_swap (f := fun s t : ℝ => F (s,t)) hF).symm
    _ = -(∫ s, φ s ∂μ) := by simp only [hleft,integral_neg]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Positive source increments between almost every pair of times -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem cumulative_increment (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s t : ℝ} (hst : s ≤ t) :
    cumulative μ t-cumulative μ s = μ.real (Ioc s t) := by
  rw [cumulative,cumulative,← measureReal_sdiff (Iic_subset_Iic.mpr hst) measurableSet_Iic]
  congr 1
  ext x
  simp only [mem_sdiff,mem_Iic,mem_Ioc,not_le]
  tauto

theorem ae_interval_balance {a b c : ℝ} {f g : ℝ → ℝ}
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hg : Integrable g)
    (hν : ∀ t, cumulative ν t = ∫ s in Iic t, g s)
    (hf : ∀ᵐ t ∂volume, t ∈ Ioo a b → f t = c+cumulative μ t-cumulative ν t) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      f t+(∫ r in s..t, g r) = f s+μ.real (Ioc s t) := by
  filter_upwards [hf] with s hs
  filter_upwards [hf] with t ht
  intro hsa hta hst
  have hμ := cumulative_increment μ hst
  have hν' := intervalIntegral.integral_Iic_sub_Iic (a := s) (b := t)
    hg.integrableOn hg.integrableOn
  rw [← hν t,← hν s] at hν'
  linarith only [hs hsa,ht hta,hμ,hν']

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
