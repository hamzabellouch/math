import OAI.Probability.InvariantIsing.Spectral.SpectralDensityContinuity

namespace OAI

/-! Right roots of the reconstructed finite spectral-group paths. The
deficit is constant below the total path's right root, including root zero. -/

noncomputable section

open MeasureTheory Set Filter Function
open scoped BigOperators Topology

namespace InvariantIsing

lemma OverlapPath.rightLim_mem_unit (p : OverlapPath) :
    Function.rightLim p.val 0 ∈ Icc (0 : ℝ) 1 :=
  ⟨(p.nonneg 0).trans (p.monotone.le_rightLim le_rfl),
    (p.monotone.rightLim_le zero_lt_one).trans (p.le_one 1)⟩

lemma OverlapPath.rightLim_le_of_pos (p : OverlapPath) {u : ℝ} (hu : 0 < u) :
    Function.rightLim p.val 0 ≤ p u := p.monotone.rightLim_le hu

lemma deficit_eq_one_sub_mean_of_le_rightLim (p : OverlapPath) {r : ℝ}
    (hr : r ≤ Function.rightLim p.val 0) :
    deficit p r = 1 - ∫ s, p s ∂pathMeasure := by
  have he : (fun s => max (p s - r) 0) =ᵐ[pathMeasure] fun s => p s - r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact max_eq_left (sub_nonneg.mpr (hr.trans (p.rightLim_le_of_pos hs.1)))
  unfold deficit
  rw [integral_congr_ae he, integral_sub p.integrable (integrable_const r)]
  simp only [integral_const, probReal_univ, one_smul]
  ring

lemma deficit_eq_at_rightLim_of_le (p : OverlapPath) {r : ℝ}
    (hr : r ≤ Function.rightLim p.val 0) :
    deficit p r = deficit p (Function.rightLim p.val 0) := by
  rw [deficit_eq_one_sub_mean_of_le_rightLim p hr,
    deficit_eq_one_sub_mean_of_le_rightLim p le_rfl]

variable {ι : Type*} [Fintype ι]

lemma spectralPathDensity_eq_at_rightLim (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) {r : ℝ}
    (hr : r ≤ Function.rightLim p.val 0) :
    spectralPathDensity ρ eig hρ hρsum p a r =
      projectedResolventDerivative ρ eig hρ hρsum a (deficit p (Function.rightLim p.val 0)) := by
  unfold spectralPathDensity
  rw [deficit_eq_at_rightLim_of_le p hr]

lemma integral_spectralDensity_rightLim (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    (∫ r in 0..Function.rightLim p.val 0, spectralPathDensity ρ eig hρ hρsum p a r) =
      Function.rightLim p.val 0 * projectedResolventDerivative ρ eig hρ hρsum a
        (deficit p (Function.rightLim p.val 0)) := by
  calc
    _ = ∫ _r in 0..Function.rightLim p.val 0, projectedResolventDerivative ρ eig hρ hρsum a
        (deficit p (Function.rightLim p.val 0)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le p.rightLim_mem_unit.1
      intro r hr
      exact spectralPathDensity_eq_at_rightLim ρ eig hρ hρsum p a hr.2.le
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

/-- The reconstructed group path has the exact root prescribed by the
root Ward equations, with no assumption that the total path is continuous. -/
theorem spectralGroupPath_root_tendsto (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    Tendsto (spectralGroupPath ρ eig hρ hρsum p a) (𝓝[>] (0 : ℝ))
      (𝓝 (Function.rightLim p.val 0 * projectedResolventDerivative ρ eig hρ hρsum a
        (deficit p (Function.rightLim p.val 0)))) := by
  have hc := continuous_spectralPathDensity ρ eig hρ hρsum p a
  have hG : Continuous (fun q => ∫ r in 0..q, spectralPathDensity ρ eig hρ hρsum p a r) :=
    intervalIntegral.continuous_primitive (fun s t => hc.intervalIntegrable s t) 0
  have ht := hG.continuousAt.tendsto.comp (p.monotone.tendsto_rightLim 0)
  rw [integral_spectralDensity_rightLim ρ eig hρ hρsum p a] at ht
  exact ht

theorem spectralGroupPath_rightLim (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    Function.rightLim (spectralGroupPath ρ eig hρ hρsum p a) 0 =
      Function.rightLim p.val 0 * projectedResolventDerivative ρ eig hρ hρsum a
        (deficit p (Function.rightLim p.val 0)) :=
  rightLim_eq_of_tendsto (spectralGroupPath_root_tendsto ρ eig hρ hρsum p a)

theorem sum_spectralGroupPath_rightLim (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) :
    (∑ a, Function.rightLim (spectralGroupPath ρ eig hρ hρsum p a) 0) =
      Function.rightLim p.val 0 := by
  simp only [spectralGroupPath_rightLim, ← Finset.mul_sum, sum_projectedResolventDerivative, mul_one]

end InvariantIsing

end

end OAI
