import OAI.Probability.IsingPerceptron.PartitionPowLe

namespace OAI

/-! Passing the Gaussian variance bound from finite leaf cutoffs to their limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace InvariantIsing

/-- Fatou's lemma for centered squares. This permits finite-leaf Gaussian
variance estimates to pass to the countable cascade prior. -/
theorem variance_le_of_ae_tendsto_of_mean_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (ht : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (hm : Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)))
    (hv : ∀ n, variance (f n) μ ≤ C) : variance g μ ≤ C := by
  let F := fun n ω => (f n ω - ∫ z, f n z ∂μ) ^ 2
  let G := fun ω => (g ω - ∫ z, g z ∂μ) ^ 2
  have hFi (n : ℕ) : Integrable (F n) μ :=
    ((hf n).sub (memLp_const _)).integrable_sq
  have hGi : Integrable G μ := (hg.sub (memLp_const _)).integrable_sq
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => ENNReal.ofReal (F n ω)) atTop (𝓝 (ENNReal.ofReal (G ω))) := by
    filter_upwards [ht] with ω hω
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hω.sub hm).pow 2)
  have hfatou : (∫⁻ ω, ENNReal.ofReal (G ω) ∂μ) ≤
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) atTop := by
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (F n ω)) atTop ∂μ :=
        lintegral_congr_ae (hlim.mono fun _ hω => hω.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' (fun n => (hFi n).aemeasurable.ennreal_ofReal)
  have hpoint (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFi n) (ae_of_all _ fun _ => sq_nonneg _)]
    change ENNReal.ofReal (∫ ω, (f n ω - ∫ z, f n z ∂μ) ^ 2 ∂μ) ≤ _
    rw [← variance_eq_integral (hf n).aemeasurable]
    exact ENNReal.ofReal_le_ofReal (hv n)
  have hb : liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂μ) atTop ≤ ENNReal.ofReal C := by
    refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (hpoint n)
  rw [← ofReal_integral_eq_lintegral_ofReal hGi (ae_of_all _ fun _ => sq_nonneg _)] at hfatou
  change ENNReal.ofReal (∫ ω, (g ω - ∫ z, g z ∂μ) ^ 2 ∂μ) ≤ _ at hfatou
  rw [← variance_eq_integral hg.aemeasurable] at hfatou
  exact (ENNReal.ofReal_le_ofReal_iff ((variance_nonneg (f 0) μ).trans (hv 0))).mp (hfatou.trans hb)

end InvariantIsing

end

end OAI
