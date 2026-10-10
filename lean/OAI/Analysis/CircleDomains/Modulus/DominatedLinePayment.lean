import OAI.Analysis.CircleDomains.Sobolev.SobolevTypicalLinePayment

namespace OAI

/-! Passing one-dimensional derivative payment to a pointwise limit,
with the actual almost-everywhere derivative limit as payment density. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma line_payment_of_dominated_derivatives
    {f : ℕ → ℝ → ℝ} {u g P : ℝ → ℝ}
    (hf : ∀ n, ContDiff ℝ 1 (f n))
    (hu : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (u x)))
    (hP : LocallyIntegrable P volume)
    (hdom : ∀ᵐ x ∂volume, ∀ n, |deriv (f n) x| ≤ P x)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => deriv (f n) x) atTop (𝓝 (g x))) :
    ∀ x z : ℝ, IntervalIntegrable g volume x z ∧
      |u x-u z| ≤ ∫ t in uIoc x z, |g t| := by
  have hgm : AEStronglyMeasurable g volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (hf n).continuous_deriv_one.aestronglyMeasurable) hlim
  have hgb : ∀ᵐ t ∂volume, ‖g t‖ ≤ P t := by
    filter_upwards [hdom, hlim] with t ht hl
    exact le_of_tendsto hl.norm (Eventually.of_forall fun n => by simpa only [Real.norm_eq_abs] using ht n)
  intro x z
  have hPi : IntegrableOn P (uIoc x z) volume :=
    (hP.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have hgi : IntegrableOn g (uIoc x z) volume :=
    hPi.mono' hgm.restrict (ae_restrict_of_ae hgb)
  refine ⟨intervalIntegrable_iff.mpr hgi, ?_⟩
  have hi : Tendsto (fun n => ∫ t in uIoc x z, |deriv (f n) t|) atTop
      (𝓝 (∫ t in uIoc x z, |g t|)) := by
    apply tendsto_integral_of_dominated_convergence P
      (fun n => (hf n).continuous_deriv_one.abs.aestronglyMeasurable.restrict) hPi
    · intro n
      filter_upwards [ae_restrict_of_ae hdom] with t ht
      simpa only [Real.norm_eq_abs, abs_abs] using ht n
    · filter_upwards [ae_restrict_of_ae hlim] with t ht
      exact ht.abs
  have hpay (n : ℕ) : |f n x-f n z| ≤ ∫ t in uIoc x z, |deriv (f n) t| :=
    smooth_line_increment_payment_ae (hf n)
      ((hf n).continuous_deriv_one.abs.intervalIntegrable x z)
      (Eventually.of_forall fun _ => le_rfl)
  exact le_of_tendsto_of_tendsto ((hu x).sub (hu z)).abs hi (Eventually.of_forall hpay)


lemma line_integral_eq_sub_of_dominated_derivatives
    {f : ℕ → ℝ → ℝ} {u g P : ℝ → ℝ}
    (hf : ∀ n, ContDiff ℝ 1 (f n))
    (hu : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (u x)))
    (hP : LocallyIntegrable P volume)
    (hdom : ∀ᵐ x ∂volume, ∀ n, |deriv (f n) x| ≤ P x)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => deriv (f n) x) atTop (𝓝 (g x))) :
    ∀ x z : ℝ, (∫ t in x..z, g t) = u z-u x := by
  intro x z
  wlog horder : x ≤ z generalizing x z
  · have he := this z x (le_of_not_ge horder)
    rw [intervalIntegral.integral_symm z x, he]
    ring
  have hPi : IntegrableOn P (Ioc x z) volume :=
    (hP.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hi : Tendsto (fun n => ∫ t in Ioc x z, deriv (f n) t) atTop
      (𝓝 (∫ t in Ioc x z, g t)) := by
    apply tendsto_integral_of_dominated_convergence P
      (fun n => (hf n).continuous_deriv_one.aestronglyMeasurable.restrict) hPi
    · intro n
      filter_upwards [ae_restrict_of_ae hdom] with t ht
      simpa only [Real.norm_eq_abs] using ht n
    · exact ae_restrict_of_ae hlim
  have heq (n : ℕ) : (∫ t in Ioc x z, deriv (f n) t) = f n z-f n x := by
    rw [← intervalIntegral.integral_of_le horder]
    exact intervalIntegral.integral_deriv_eq_sub
      (fun _ _ => (hf n).differentiable_one _) ((hf n).continuous_deriv_one.intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le horder]
  exact tendsto_nhds_unique hi (by simpa only [heq] using (hu z).sub (hu x))

end CircleDomainRigidity

end

end OAI
