import Mathlib

namespace OAI

section

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace TamingCompatibility
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma tendstoInMeasure_of_integral_nonneg {ι : Type*} {l : Filter ι}
    (f : ι → Ω → ℝ) (hf : ∀ n, Integrable (f n) μ)
    (hp : ∀ n, 0 ≤ᵐ[μ] f n)
    (hl : Tendsto (fun n => ∫ x, f n x ∂μ) l (𝓝 0)) :
    TendstoInMeasure μ f l (fun _ => 0) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
  have he (n : ι) : eLpNorm (f n - (fun _ => 0)) 1 μ = ENNReal.ofReal (∫ x, f n x ∂μ) := by
    simp only [eLpNorm_one_eq_lintegral_enorm
      ((hf n).aestronglyMeasurable.sub aestronglyMeasurable_const),Pi.sub_apply,sub_zero]
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hf n)]
    congr 1
    apply integral_congr_ae
    filter_upwards [hp n] with x hx
    exact Real.norm_of_nonneg hx
  simpa only [he,ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hl

lemma integral_weight_mul_tendsto_zero_of_inMeasure
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (f : ι → Ω → ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (C : ℝ) (hp : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C)
    (hl : TendstoInMeasure μ f l (fun _ => 0))
    (g : Ω → ℝ) (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x, g x * f n x ∂μ) l (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms,_,hms⟩ := (hl.comp hns).exists_seq_tendsto_ae
  refine ⟨ms,?_⟩
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => g x*f (ns (ms n)) x) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hms] with x hx
    simpa only [Function.comp_apply,mul_zero] using tendsto_const_nhds.mul hx
  have hh := tendsto_integral_of_dominated_convergence (fun x => ‖g x‖*C)
    (fun n => hg.aestronglyMeasurable.mul (hf _)) (hg.norm.mul_const C)
    (fun n => (hp (ns (ms n))).mono (fun x hx => by
      rw [Pi.mul_apply,norm_mul]
      exact mul_le_mul_of_nonneg_left hx (norm_nonneg _))) hlim
  simpa only [integral_zero,Pi.mul_apply] using hh

lemma integral_weight_mul_tendsto_zero_of_bounded_mass
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (f : ι → Ω → ℝ) (hf : ∀ n, Integrable (f n) μ)
    (C : ℝ) (hp : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x ∧ f n x ≤ C)
    (hl : Tendsto (fun n => ∫ x, f n x ∂μ) l (𝓝 0))
    (g : Ω → ℝ) (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x, g x * f n x ∂μ) l (𝓝 0) := by
  apply integral_weight_mul_tendsto_zero_of_inMeasure f (fun n => (hf n).aestronglyMeasurable) C
  · intro n
    filter_upwards [hp n] with x hx
    simpa only [Real.norm_of_nonneg hx.1] using hx.2
  · exact tendstoInMeasure_of_integral_nonneg f hf (fun n => (hp n).mono fun _ h => h.1) hl
  · exact hg
end TamingCompatibility

end
end

section

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace TamingCompatibility
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma sqrt_memLp_two (f : Ω → ℝ) (hi : Integrable f μ) (hp : ∀ x, 0 ≤ f x) :
    MemLp (fun x => Real.sqrt (f x)) 2 μ := by
  rw [memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hi.aestronglyMeasurable)]
  simpa only [Real.sq_sqrt (hp _)] using hi

lemma integral_sqrt_mul_sqrt_le (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfp : ∀ x, 0 ≤ f x) (hgp : ∀ x, 0 ≤ g x) :
    (∫ x, Real.sqrt (f x)*Real.sqrt (g x) ∂μ) ≤
      Real.sqrt (∫ x, f x ∂μ)*Real.sqrt (∫ x, g x ∂μ) := by
  have hf' := sqrt_memLp_two f hf hfp
  have hg' := sqrt_memLp_two g hg hgp
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all μ fun x => Real.sqrt_nonneg (f x)) (ae_of_all μ fun x => Real.sqrt_nonneg (g x))
    (show MemLp (fun x => Real.sqrt (f x)) (ENNReal.ofReal (2:ℝ)) μ by simpa using hf')
    (show MemLp (fun x => Real.sqrt (g x)) (ENNReal.ofReal (2:ℝ)) μ by simpa using hg')
  simp only [Real.rpow_two,Real.sq_sqrt (hfp _),Real.sq_sqrt (hgp _)] at hh
  simpa only [Real.sqrt_eq_rpow,one_div] using hh

lemma integral_sqrt_mul_sqrt_tendsto {ι : Type*} {l : Filter ι}
    (f g : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ) (hg : ∀ i, Integrable (g i) μ)
    (hfp : ∀ i x, 0 ≤ f i x) (hgp : ∀ i x, 0 ≤ g i x)
    (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ᶠ i in l, (∫ x, f i x ∂μ) ≤ C)
    (hl : Tendsto (fun i => ∫ x, g i x ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, Real.sqrt (f i x)*Real.sqrt (g i x) ∂μ) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun i => integral_nonneg fun x => by positivity)
  · filter_upwards [hb] with i hi
    exact (integral_sqrt_mul_sqrt_le (f i) (g i) (hf i) (hg i) (hfp i) (hgp i)).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hi) (Real.sqrt_nonneg _))
  · simpa only [Real.sqrt_zero,mul_zero,Function.comp_def] using
      (tendsto_const_nhds (x := Real.sqrt C)).mul (Real.continuous_sqrt.tendsto 0 |>.comp hl)
end TamingCompatibility

end
end

end OAI
