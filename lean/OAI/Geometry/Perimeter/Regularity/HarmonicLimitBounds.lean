import OAI.Geometry.Perimeter.Regularity.GeoComposition

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem integral_norm_le_of_L1_limit {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : ℕ → X → ℝ) (hf : ∀ i, Integrable (f i) μ)
    {g : X → ℝ} (hg : Integrable g μ) {V : ℝ}
    (hb : ∀ i, ∫ x, ‖f i x‖ ∂μ ≤ V)
    (hL : Tendsto (fun i ↦ ∫⁻ x, ‖f i x-g x‖ₑ ∂μ) atTop (𝓝 0)) :
    ∫ x, ‖g x‖ ∂μ ≤ V := by
  have hn : Tendsto (fun i ↦ ∫⁻ x, ‖‖f i x‖-‖g x‖‖ₑ ∂μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hL
      (Eventually.of_forall fun _ ↦ zero_le)
    exact Eventually.of_forall fun i ↦ lintegral_mono fun x ↦ by
      rw [← ofReal_norm,← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (f i x) (g x))
  exact le_of_tendsto' (tendsto_integral_of_L1 (fun x ↦ ‖g x‖)
    hg.norm.aestronglyMeasurable (Eventually.of_forall fun i ↦ (hf i).norm) hn) hb

theorem kernelLinear_uniform_bound {k : Euc n → ℝ}
    (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    ∃ M : ℝ, 0≤M ∧ ∀ u : Euc n → ℝ, Integrable u volume →
      ‖kernelLinear u k‖≤M*(∫ x, ‖u x‖) := by
  obtain ⟨M,hM⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hk.continuous_fderiv (by simp))
  refine ⟨M,(norm_nonneg _).trans (hM 0),fun u hu ↦ ?_⟩
  apply (norm_integral_le_integral_norm _).trans
  have h := integral_mono_ae (kernelLinear_integrable hu hk hc).norm (hu.norm.const_mul M)
    (ae_of_all _ fun x ↦ show ‖u x • fderiv ℝ k (-x)‖≤M*‖u x‖ from by
      rw [norm_smul,mul_comm M]
      exact mul_le_mul_of_nonneg_left (hM (-x)) (norm_nonneg _))
  simpa only [integral_const_mul] using h

theorem harmonicRegularization_uniform_taylor (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ u : Euc n → ℝ, Integrable u volume → ∀ y : Euc n,
      ‖harmonicRegularization u 4 y-harmonicRegularization u 4 0-
        kernelLinear u (scaledHarmonicKernel 4) y‖ ≤ C*(∫ x, ‖u x‖)*‖y‖^2 := by
  exact convolution_uniform_taylor (scaledHarmonicKernel_contDiff 4)
    ((isCompact_closedBall 0 (1/(4:ℝ))).of_isClosed_subset (isClosed_tsupport _)
      (scaledHarmonicKernel_tsupport (by norm_num)))

theorem harmonic_height_representative_bounds (hn : 0<n) :
    ∃ C : ℝ, 0≤C ∧ ∀ g : Euc n → ℝ, Integrable g volume →
      WeakHarmonicOn g (Metric.ball 0 1) → ∀ V : ℝ, (∫ x, ‖g x‖)≤V →
      ∃ w : Euc n → ℝ, ∃ ℓ : Euc n →L[ℝ] ℝ,
        ContDiff ℝ ∞ w ∧ g =ᵐ[volume.restrict (Metric.ball 0 (1/2))] w ∧
        ∀ y, ‖w y-w 0-ℓ y‖≤C*V*‖y‖^2 := by
  obtain ⟨C,hC,hTaylor⟩ := harmonicRegularization_uniform_taylor n
  refine ⟨C,hC,fun g hg hw V hV ↦ ⟨harmonicRegularization g 4,
    kernelLinear g (scaledHarmonicKernel 4),
    harmonicRegularization_contDiff hg.locallyIntegrable (by norm_num),?_,?_⟩⟩
  · filter_upwards [ae_restrict_of_ae (weakHarmonic_ae_eq_regularization hg.locallyIntegrable hw hn),
      ae_restrict_mem measurableSet_ball] with y hy hyB
    apply hy (1/2) (by norm_num) _ 4 (by norm_num)
    intro z hz
    have hd := dist_triangle z y 0
    rw [Metric.mem_ball] at hz hyB ⊢
    linarith
  · intro y
    exact (hTaylor g hg y).trans (by gcongr)

end RPISingularHarnack

end

end OAI
