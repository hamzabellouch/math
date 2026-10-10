import OAI.Geometry.Perimeter.Regularity.GeoAlgebra

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap
variable {n : ℕ}

theorem c1Mollify_norm_le_bound {ψ : Euc n → ℝ} (hψ : Continuous ψ)
    {M : ℝ} (hM : ∀ x, ‖ψ x‖ ≤ M) (j : ℕ) (y : Euc n) :
    ‖c1Mollify ψ j y‖ ≤ M := by
  let k : Euc n → ℝ := (c1Mollifier j).normed volume
  have hk : Integrable k volume := (c1Mollifier j).integrable_normed
  have hp : ∀ x, 0 ≤ k x := (c1Mollifier j).nonneg_normed
  have hi : Integrable (fun x ↦ k x*ψ (y-x)) volume :=
    hk.mul_bdd (hψ.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun x ↦ hM _)
  change ‖∫ x, k x*ψ (y-x)‖ ≤ M
  calc
    _ ≤ ∫ x, ‖k x*ψ (y-x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, k x*M := by
      apply integral_mono hi.norm (hk.mul_const M)
      intro x
      change ‖k x*ψ (y-x)‖ ≤ k x*M
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hp x)]
      exact mul_le_mul_of_nonneg_left (hM _) (hp x)
    _ = M := by rw [integral_mul_const]; dsimp only [k]; rw [(c1Mollifier j).integral_normed,one_mul]

theorem weak_c1_convolution_identity (μ : Measure (Euc n)) [SFinite μ]
    {f : Euc n → ℝ} (hf : Integrable f μ) {ψ : Euc n → ℝ}
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (j : ℕ) :
    (∫ x, ψ x*(f ⋆[lsmul ℝ ℝ, μ] (c1Mollifier j).normed volume) x) =
      ∫ y, f y*c1Mollify ψ j y ∂μ := by
  let k : Euc n → ℝ := (c1Mollifier j).normed volume
  obtain ⟨M,hM⟩ := hcψ.exists_bound_of_continuous hψ
  have hi : Integrable (fun z : Euc n × Euc n ↦ ψ z.1*(f z.2*k (z.1-z.2)))
      (volume.prod μ) :=
    (hf.convolution_integrand (lsmul ℝ ℝ) (c1Mollifier j).integrable_normed).bdd_mul
      (hψ.comp continuous_fst).aestronglyMeasurable (ae_of_all _ fun z ↦ hM _)
  calc
    _ = ∫ x, ∫ y, ψ x*(f y*k (x-y)) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ (integral_const_mul _ _).symm
    _ = ∫ y, ∫ x, ψ x*(f y*k (x-y)) ∂volume ∂μ := integral_integral_swap hi
    _ = ∫ y, f y*c1Mollify ψ j y ∂μ := by
      apply integral_congr_ae
      apply ae_of_all
      intro y
      dsimp only
      rw [c1Mollify,convolution_eq_swap,← integral_const_mul]
      apply integral_congr_ae
      apply ae_of_all
      intro x
      change ψ x*(f y*k (x-y)) = f y*(k (y-x)*ψ x)
      have he : k (y-x) = k (x-y) := by
        rw [show y-x=-(x-y) by abel]
        exact (c1Mollifier j).normed_neg _
      rw [he]
      ring

theorem weak_c1_convolution_tendsto (μ : Measure (Euc n)) [SFinite μ]
    {f : Euc n → ℝ} (hf : Integrable f μ) {ψ : Euc n → ℝ}
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Tendsto (fun j ↦ ∫ x, ψ x*(f ⋆[lsmul ℝ ℝ, μ] (c1Mollifier j).normed volume) x)
      atTop (𝓝 (∫ y, ψ y*f y ∂μ)) := by
  simp_rw [weak_c1_convolution_identity μ hf hψ hcψ]
  obtain ⟨M,hM⟩ := hcψ.exists_bound_of_continuous hψ
  have h : Tendsto (fun j ↦ ∫ y, f y*c1Mollify ψ j y ∂μ) atTop
      (𝓝 (∫ y, f y*ψ y ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun y ↦ ‖f y‖*M)
    · intro j
      exact hf.aestronglyMeasurable.mul (c1Mollify_contDiff hψ j).continuous.aestronglyMeasurable
    · exact hf.norm.mul_const M
    · intro j
      apply ae_of_all
      intro y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (c1Mollify_norm_le_bound hψ hM j y) (norm_nonneg _)
    · exact ae_of_all _ fun y ↦ tendsto_const_nhds.mul (c1Mollify_tendsto hψ y)
  convert h using 2
  apply integral_congr_ae
  exact ae_of_all _ fun y ↦ mul_comm _ _

theorem weak_c1_convolution_tendsto_of_ae_continuous
    (μ : Measure (Euc n)) [SFinite μ] {f : Euc n → ℝ} (hf : Integrable f μ)
    {ψ : Euc n → ℝ} (hψ : Measurable ψ) {M : ℝ} (hM : ∀ x, ‖ψ x‖ ≤ M)
    (hcont : ∀ᵐ y ∂μ, ContinuousAt ψ y) :
    Tendsto (fun j ↦ ∫ x, ψ x*(f ⋆[lsmul ℝ ℝ, μ] (c1Mollifier j).normed volume) x)
      atTop (𝓝 (∫ y, ψ y*f y ∂μ)) := by
  have hM0 : 0 ≤ M := (norm_nonneg (ψ 0)).trans (hM 0)
  have hloc : LocallyIntegrable ψ volume :=
    (locallyIntegrable_const M).mono hψ.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs,abs_of_nonneg hM0] using hM x)
  have hc (j : ℕ) : ContDiff ℝ ∞ (c1Mollify ψ j) :=
    (c1Mollifier j).hasCompactSupport_normed.contDiff_convolution_left _
      (c1Mollifier j).contDiff_normed hloc
  have hbound (j : ℕ) (y : Euc n) : ‖c1Mollify ψ j y‖ ≤ M := by
    let k : Euc n → ℝ := (c1Mollifier j).normed volume
    have hk : Integrable k volume := (c1Mollifier j).integrable_normed
    have hp : ∀ x, 0 ≤ k x := (c1Mollifier j).nonneg_normed
    have hi : Integrable (fun x ↦ k x*ψ (y-x)) volume :=
      hk.mul_bdd (hψ.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
        (ae_of_all _ fun x ↦ hM _)
    change ‖∫ x, k x*ψ (y-x)‖ ≤ M
    calc
      _ ≤ ∫ x, ‖k x*ψ (y-x)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, k x*M := by
        apply integral_mono hi.norm (hk.mul_const M)
        intro x
        change ‖k x*ψ (y-x)‖ ≤ k x*M
        rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hp x)]
        exact mul_le_mul_of_nonneg_left (hM _) (hp x)
      _ = M := by rw [integral_mul_const]; dsimp only [k]; rw [(c1Mollifier j).integral_normed,one_mul]
  have he (j : ℕ) :
      (∫ x, ψ x*(f ⋆[lsmul ℝ ℝ, μ] (c1Mollifier j).normed volume) x) =
        ∫ y, f y*c1Mollify ψ j y ∂μ := by
    let k : Euc n → ℝ := (c1Mollifier j).normed volume
    have hi : Integrable (fun z : Euc n × Euc n ↦ ψ z.1*(f z.2*k (z.1-z.2)))
        (volume.prod μ) :=
      (hf.convolution_integrand (lsmul ℝ ℝ) (c1Mollifier j).integrable_normed).bdd_mul
        (hψ.comp measurable_fst).aestronglyMeasurable (ae_of_all _ fun z ↦ hM _)
    calc
      _ = ∫ x, ∫ y, ψ x*(f y*k (x-y)) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun x ↦ (integral_const_mul _ _).symm
      _ = ∫ y, ∫ x, ψ x*(f y*k (x-y)) ∂volume ∂μ := integral_integral_swap hi
      _ = ∫ y, f y*c1Mollify ψ j y ∂μ := by
        apply integral_congr_ae
        apply ae_of_all
        intro y
        dsimp only
        rw [c1Mollify,convolution_eq_swap,← integral_const_mul]
        apply integral_congr_ae
        apply ae_of_all
        intro x
        change ψ x*(f y*k (x-y)) = f y*(k (y-x)*ψ x)
        have hk : k (y-x) = k (x-y) := by
          rw [show y-x=-(x-y) by abel]
          exact (c1Mollifier j).normed_neg _
        rw [hk]; ring
  simp_rw [he]
  have ht : Tendsto (fun j ↦ ∫ y, f y*c1Mollify ψ j y ∂μ) atTop
      (𝓝 (∫ y, f y*ψ y ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun y ↦ ‖f y‖*M)
    · exact fun j ↦ hf.aestronglyMeasurable.mul (hc j).continuous.aestronglyMeasurable
    · exact hf.norm.mul_const M
    · intro j
      apply ae_of_all
      intro y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hbound j y) (norm_nonneg _)
    · filter_upwards [hcont] with y hy
      apply tendsto_const_nhds.mul
      exact ContDiffBump.convolution_tendsto_right c1Mollifier_radius_tendsto
        (Eventually.of_forall fun _ ↦ hψ.aestronglyMeasurable)
        (hy.tendsto.comp tendsto_snd) tendsto_const_nhds
  convert ht using 2
  apply integral_congr_ae
  exact ae_of_all _ fun y ↦ mul_comm _ _

end RPISingularHarnack

end

end OAI
