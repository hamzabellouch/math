import OAI.Analysis.FreeEntropy.GaussianConvolution

namespace OAI

universe u1 u2 u3

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι]
 theorem map_withDensity_of_measurePreserving {α : Type u2} {β : Type u3} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β} (hf : MeasurePreserving f μ ν)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity (g ∘ f)).map f = ν.withDensity g := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hf.measurable]
  change (∫⁻ a,(F ∘ f) a ∂μ.withDensity (g ∘ f)) = _
  rw [lintegral_withDensity_eq_lintegral_mul μ (hg.comp hf.measurable) (hF.comp hf.measurable),lintegral_withDensity_eq_lintegral_mul ν hg hF]
  exact hf.lintegral_comp (hg.mul hF)
 theorem productNormal_withDensity {s : ℝ} (hs : 0<s) :
    Measure.pi (fun _ : ι => gaussianReal 0 (⟨s,hs.le⟩ : ℝ≥0)) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏i,gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0) (x i))) := by
  classical
  have hv : (⟨s,hs.le⟩ : ℝ≥0)≠0 := by
    intro h; exact hs.ne' (congrArg (fun x : ℝ≥0 => (x:ℝ)) h)
  have hi : Integrable (fun x : ι → ℝ => ∏i,gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0) (x i)) :=
    Integrable.fintype_prod (fun _ => integrable_gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0))
  let v : ℝ≥0 := ⟨s,hs.le⟩
  have : ∀i : ι,SigmaFinite (gaussianReal 0 v) := fun _ => inferInstance
  apply Measure.pi_eq (μ := fun _ : ι => gaussianReal 0 v)
  intro S hS
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS)]
  rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn (ae_of_all _ (fun x => prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)))]
  rw [integral_pi_prod _ S hS,ENNReal.ofReal_prod_of_nonneg]
  · apply prod_congr rfl
    intro i _
    rw [gaussianReal_apply 0 hv]
    exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0)).integrableOn
      (ae_of_all _ (gaussianPDFReal_nonneg _ _))
  · intro i _
    exact integral_nonneg (gaussianPDFReal_nonneg _ _)
 def normalLaw (s : ℝ) : Measure (EuclideanSpace ℝ ι) :=
    volume.withDensity (fun x => ENNReal.ofReal (normalKernel s x))
 theorem normalLaw_eq_map {s : ℝ} (hs : 0<s) :
    normalLaw (ι := ι) s = (Measure.pi (fun _ : ι => gaussianReal 0 (⟨s,hs.le⟩ : ℝ≥0))).map (WithLp.toLp 2) := by
  rw [productNormal_withDensity hs]
  have he : (fun x : ι → ℝ => ENNReal.ofReal (∏i,gaussianPDFReal 0 (⟨s,hs.le⟩ : ℝ≥0) (x i))) =
       (fun x => ENNReal.ofReal (normalKernel s x)) ∘ WithLp.toLp 2 := by
    funext x; simp only [Function.comp_apply,normalKernel_product hs]
  rw [he]
  exact (map_withDensity_of_measurePreserving (PiLp.volume_preserving_toLp ι)
    (fun x => ENNReal.ofReal (normalKernel s x))
    (ENNReal.measurable_ofReal.comp (normalKernel_continuous_space s).measurable)).symm
 theorem normalLaw_eq_scaled {s : ℝ} (hs : 0<s) :
    normalLaw (ι := ι) s = (productGaussian ι).map (fun x => Real.sqrt s • WithLp.toLp 2 x) := by
  have hm : (productGaussian ι).map (fun x i => Real.sqrt s*x i) = Measure.pi (fun _ : ι => gaussianReal 0 (⟨s,hs.le⟩ : ℝ≥0)) := by
    change (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x i => Real.sqrt s * id (x i)) = _
    rw [Measure.pi_map_pi (fun _ => (measurable_id.const_mul (Real.sqrt s)).aemeasurable)]
    congr 1
    funext i
    simp only [id_eq]
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp only [mul_one,NNReal.coe_mk,Real.sq_sqrt hs.le]
      rfl
  rw [normalLaw_eq_map hs,← hm]
  rw [Measure.map_map (show Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) from (PiLp.continuous_toLp 2 _).measurable) (by fun_prop)]
  congr 1
 theorem normalLaw_probability {s : ℝ} (hs : 0<s) : IsProbabilityMeasure (normalLaw (ι := ι) s) := by
  rw [normalLaw_eq_scaled hs]
  infer_instance
 theorem smoothedLaw_eq (μ : Measure (EuclideanSpace ℝ ι)) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0<s) :
    (μ.prod (normalLaw s)).map (fun z => z.1+z.2) =
      volume.withDensity (fun x => ENNReal.ofReal (smoothedDensity μ s x)) := by
  have : IsProbabilityMeasure (normalLaw (ι := ι) s) := normalLaw_probability hs
  have hk := (ENNReal.measurable_ofReal.comp (normalKernel_continuous_space (ι := ι) s).measurable)
  have hden := (ENNReal.measurable_ofReal.comp (smoothedDensity_continuous μ hs).measurable)
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (by fun_prop)]
  rw [lintegral_prod _ (show AEMeasurable (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => F (z.1+z.2)) _ from (hF.comp (by fun_prop)).aemeasurable)]
  have hinner (a : EuclideanSpace ℝ ι) :
      (∫⁻z,F (a+z) ∂normalLaw s) = ∫⁻z,ENNReal.ofReal (normalKernel s z)*F (a+z) := by
    exact lintegral_withDensity_eq_lintegral_mul volume hk (show Measurable (fun z => F (a+z)) from hF.comp (measurable_const.add measurable_id))
  simp_rw [hinner]
  have hshift (a : EuclideanSpace ℝ ι) :
      (∫⁻z,ENNReal.ofReal (normalKernel s z)*F (a+z)) =
      ∫⁻x,ENNReal.ofReal (normalKernel s (x-a))*F x := by
    have he := (measurePreserving_add_left (volume : Measure (EuclideanSpace ℝ ι)) a).lintegral_comp
      (f := fun x => ENNReal.ofReal (normalKernel s (x-a))*F x)
      ((hk.comp (measurable_id.sub measurable_const)).mul hF)
    simpa only [add_sub_cancel_left] using he
  simp_rw [hshift]
  have hmeas : Measurable (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
      ENNReal.ofReal (normalKernel s (z.2-z.1))*F z.2) :=
    (hk.comp (measurable_snd.sub measurable_fst)).mul (hF.comp measurable_snd)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  change (∫⁻x,∫⁻a,ENNReal.ofReal (normalKernel s (x-a))*F x ∂μ) = ∫⁻x,F x ∂volume.withDensity (ENNReal.ofReal ∘ smoothedDensity μ s)
  rw [lintegral_withDensity_eq_lintegral_mul volume hden hF]
  apply lintegral_congr
  intro x
  rw [lintegral_mul_const (F x) (show Measurable (fun a => ENNReal.ofReal (normalKernel s (x-a))) from hk.comp (measurable_const.sub measurable_id)),← ofReal_integral_eq_lintegral_ofReal (normalKernel_integrable_finite μ hs x) (ae_of_all _ (fun a => (normalKernel_pos _ _).le))]
  rfl
end FiniteEntropySeparation

end

end OAI
