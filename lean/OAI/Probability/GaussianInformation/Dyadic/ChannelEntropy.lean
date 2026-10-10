import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.RefinementCost

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace RepeatedLocalization
lemma integrable_xlog_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {M : ℝ} (hfM : ∀ x,f x ≤ M) : Integrable (fun x => xlog (f x)) μ := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc (a := (0:ℝ)) (b := M)).image continuous_xlog).isBounded.exists_norm_le
  apply integrable_bounded_measurable μ _ (continuous_xlog.measurable.comp hf)
  intro x
  simpa only [Real.norm_eq_abs,Function.comp_def] using hC _ (Set.mem_image_of_mem _ ⟨hf0 x,hfM x⟩)

lemma klDiv_withDensity_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hf0 : ∀ x,0 ≤ f x) {M : ℝ} (hfM : ∀ x,f x ≤ M)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))] :
    InformationTheory.klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ =
      ENNReal.ofReal (∫ x,xlog (f x) ∂μ) := by
  have hif := integrable_bounded_measurable μ f hf (fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfM x)
  have hix := integrable_xlog_bounded μ f hf hf0 hfM
  have hib : Integrable (fun x => InformationTheory.klFun (f x)) μ :=
    (hix.add (integrable_const 1)).sub hif
  have hfint : ∫ x,f x ∂μ = 1 := by
    have h := measure_univ (μ := μ.withDensity (fun x => ENNReal.ofReal (f x)))
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hif (ae_of_all _ hf0)] at h
    exact (ENNReal.ofReal_eq_one.mp h)
  rw [InformationTheory.klDiv_eq_lintegral_klFun_of_ac (withDensity_absolutelyContinuous μ _)]
  have hrn := Measure.rnDeriv_withDensity μ hf.ennreal_ofReal
  have he : (fun x => ENNReal.ofReal (InformationTheory.klFun (((μ.withDensity
      (fun x => ENNReal.ofReal (f x))).rnDeriv μ x).toReal))) =ᵐ[μ]
      (fun x => ENNReal.ofReal (InformationTheory.klFun (f x))) := by
    filter_upwards [hrn] with x hx
    rw [hx,ENNReal.toReal_ofReal (hf0 x)]
  rw [lintegral_congr_ae he,← ofReal_integral_eq_lintegral_ofReal hib
    (ae_of_all _ (fun x => InformationTheory.klFun_nonneg (hf0 x)))]
  congr 1
  change (∫ x,xlog (f x)+1-f x ∂μ) = _
  rw [integral_sub (f := fun x => xlog (f x)+1) (hix.add (integrable_const 1)) hif,
    integral_add hix (integrable_const 1),hfint]
  simp

lemma measurable_finite_eval {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (p : ι → α → ℝ)
    (hp : ∀ i,Measurable (p i)) : Measurable (fun x : α × ι => p x.2 x.1) := by
  classical
  have he : (fun x : α × ι => p x.2 x.1) =
      fun x => ∑ i,if x.2 = i then p i x.1 else 0 := by funext x; simp
  rw [he]
  apply Finset.measurable_sum
  intro i hi
  exact ((hp i).comp measurable_fst).piecewise (measurable_snd (measurableSet_singleton i)) measurable_const

namespace FiniteChannel
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

noncomputable def law (p : FiniteChannel α ι) (μ : Measure α) : Measure (α × ι) :=
  (μ.prod Measure.count).withDensity (fun x => ENNReal.ofReal (p.prob x.2 x.1))

lemma measurable_density (p : FiniteChannel α ι) :
    Measurable (fun x : α × ι => ENNReal.ofReal (p.prob x.2 x.1)) :=
  (measurable_finite_eval p.prob p.measurable).ennreal_ofReal

lemma lintegral_law (p : FiniteChannel α ι) (μ : Measure α) [SFinite μ]
    (f : α × ι → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x,f x ∂p.law μ = ∑ i,∫⁻ x,ENNReal.ofReal (p.prob i x)*f (x,i) ∂μ := by
  rw [law,lintegral_withDensity_eq_lintegral_mul _ p.measurable_density hf,
    lintegral_prod _ (p.measurable_density.mul hf).aemeasurable]
  simp_rw [lintegral_count,tsum_fintype]
  exact lintegral_finsetSum _ (fun i _ => ((p.measurable i).ennreal_ofReal.mul
    (hf.comp (show Measurable (fun x : α => (x,i)) from measurable_id.prodMk measurable_const))))

lemma lintegral_prob {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : FiniteChannel α ι) (μ : Measure α) [IsFiniteMeasure μ] (i : ι) :
    ∫⁻ x,ENNReal.ofReal (p.prob i x) ∂μ = ENNReal.ofReal (scoreMass μ (p.prob i)) :=
  (ofReal_integral_eq_lintegral_ofReal (p.integrable μ i) (ae_of_all _ (p.nonneg i))).symm

lemma density_total {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (p : FiniteChannel α ι) (x : α) :
    ∑ i,ENNReal.ofReal (p.prob i x) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.nonneg i x),p.total]
  simp

instance law_probability (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (p.law μ) := by
  constructor
  have h := p.lintegral_law μ (fun _ => 1) measurable_const
  simp only [lintegral_const,one_mul,mul_one] at h
  rw [h]
  simp_rw [p.lintegral_prob μ]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => scoreMass_nonneg μ _ (p.nonneg i)),p.mass_total]
  simp

lemma law_fst (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    (p.law μ).map Prod.fst = μ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_fst]
  rw [p.lintegral_law μ (fun x => f x.1) (hf.comp measurable_fst)]
  change (∑ i,∫⁻ x,ENNReal.ofReal (p.prob i x)*f x ∂μ) = _
  rw [← lintegral_finsetSum Finset.univ (f := fun i x => ENNReal.ofReal (p.prob i x)*f x)
    (fun i _ => ((p.measurable i).ennreal_ofReal.mul hf))]
  simp_rw [← Finset.sum_mul,p.density_total,one_mul]

noncomputable def outputLaw (p : FiniteChannel α ι) (μ : Measure α) : Measure ι :=
  Measure.count.withDensity (fun i => ENNReal.ofReal (scoreMass μ (p.prob i)))

lemma law_snd (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    (p.law μ).map Prod.snd = p.outputLaw μ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_snd]
  rw [p.lintegral_law μ (fun x => f x.2) (hf.comp measurable_snd),
    outputLaw,lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _) hf,
    lintegral_count,tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  change (∫⁻ x,ENNReal.ofReal (p.prob i x)*f i ∂μ) = ENNReal.ofReal (scoreMass μ (p.prob i))*f i
  rw [lintegral_mul_const (f i) (p.measurable i).ennreal_ofReal, p.lintegral_prob]

instance outputLaw_probability (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (p.outputLaw μ) := by
  rw [← p.law_snd μ]
  exact (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).mpr inferInstance

lemma law_eq_sum (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    p.law μ = ∑ i, (μ.withDensity (fun x => ENNReal.ofReal (p.prob i x))).map (fun x => (x,i)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [p.lintegral_law μ _ hf,lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_map (g := fun x : α => (x,i)) hf (measurable_id.prodMk measurable_const)]
  exact (lintegral_withDensity_eq_lintegral_mul μ (p.measurable i).ennreal_ofReal
    (hf.comp (show Measurable (fun x : α => (x,i)) from measurable_id.prodMk measurable_const))).symm

noncomputable def likelihoodRatio (p : FiniteChannel α ι) (μ : Measure α) (x : α × ι) : ℝ :=
  p.prob x.2 x.1/scoreMass μ (p.prob x.2)

lemma measurable_likelihoodRatio (p : FiniteChannel α ι) (μ : Measure α) :
    Measurable (p.likelihoodRatio μ) :=
  measurable_finite_eval (fun i x => p.prob i x/scoreMass μ (p.prob i))
    (fun i => (p.measurable i).div_const _)

lemma likelihoodRatio_nonneg {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : FiniteChannel α ι) (μ : Measure α) (x : α × ι) :
    0 ≤ p.likelihoodRatio μ x := div_nonneg (p.nonneg _ _) (scoreMass_nonneg μ _ (p.nonneg _))

lemma likelihoodRatio_le {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : FiniteChannel α ι) (μ : Measure α) (x : α × ι) :
    p.likelihoodRatio μ x ≤ ∑ i,1/scoreMass μ (p.prob i) := by
  classical
  exact (div_le_div_of_nonneg_right (p.le_one _ _) (scoreMass_nonneg μ _ (p.nonneg _))).trans
    (Finset.single_le_sum (fun i _ => div_nonneg zero_le_one (scoreMass_nonneg μ _ (p.nonneg i))) (Finset.mem_univ x.2))

lemma law_eq_reference_density (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    p.law μ = (μ.prod (p.outputLaw μ)).withDensity (fun x => ENNReal.ofReal (p.likelihoodRatio μ x)) := by
  unfold outputLaw
  rw [prod_withDensity_right (measurable_of_countable _),
    ← withDensity_mul (μ.prod Measure.count)
      (f := fun z : α × ι => ENNReal.ofReal (scoreMass μ (p.prob z.2)))
      (g := fun z => ENNReal.ofReal (p.likelihoodRatio μ z))
      ((measurable_of_countable (fun i : ι => ENNReal.ofReal (scoreMass μ (p.prob i)))).comp measurable_snd) (p.measurable_likelihoodRatio μ).ennreal_ofReal]
  unfold law
  apply withDensity_congr_ae
  have he (i : ι) : ∀ᵐ x ∂μ, p.prob i x = scoreMass μ (p.prob i)*(p.prob i x/scoreMass μ (p.prob i)) := by
    by_cases h : scoreMass μ (p.prob i) = 0
    · have hz := (integral_eq_zero_iff_of_nonneg (p.nonneg i) (p.integrable μ i)).mp h
      filter_upwards [hz] with x hx
      simp [h,hx]
    · exact ae_of_all _ (fun x => by field_simp)
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun p.measurable_density
      (((measurable_of_countable (fun i : ι => ENNReal.ofReal (scoreMass μ (p.prob i)))).comp measurable_snd).mul
        (p.measurable_likelihoodRatio μ).ennreal_ofReal))).mpr
  · filter_upwards [ae_all_iff.mpr he] with x hx
    exact ae_of_all _ (fun i => by
      change ENNReal.ofReal (p.prob i x) = ENNReal.ofReal (scoreMass μ (p.prob i))*ENNReal.ofReal (p.prob i x/scoreMass μ (p.prob i))
      rw [← ENNReal.ofReal_mul (scoreMass_nonneg μ _ (p.nonneg i)),← hx i])

lemma integral_xlog_ratio {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] (i : ι) :
    scoreMass μ (p.prob i)*(∫ x,xlog (p.prob i x/scoreMass μ (p.prob i)) ∂μ) =
      infoContribution μ (p.prob i) := by
  by_cases h : scoreMass μ (p.prob i) = 0
  · rw [h,zero_mul,infoContribution_zero_mass μ _ (p.measurable i) (p.nonneg i) (p.le_one i) h]
  · have he (x : α) : scoreMass μ (p.prob i)*xlog (p.prob i x/scoreMass μ (p.prob i)) =
        xlog (p.prob i x)-p.prob i x*Real.log (scoreMass μ (p.prob i)) := by
      have hx := xlog_mul (p.prob i x/scoreMass μ (p.prob i)) (scoreMass μ (p.prob i))
      rw [div_mul_cancel₀ _ h] at hx
      unfold xlog at hx ⊢
      field_simp at hx ⊢
      linarith
    rw [← integral_const_mul]
    simp_rw [he]
    rw [integral_sub (integrable_xlog_probability μ _ (p.measurable i) (p.nonneg i) (p.le_one i))
      ((p.integrable μ i).mul_const _),integral_mul_const]
    rfl

lemma klDiv_law (p : FiniteChannel α ι) (μ : Measure α) [IsProbabilityMeasure μ] :
    InformationTheory.klDiv (p.law μ) (((p.law μ).map Prod.fst).prod ((p.law μ).map Prod.snd)) =
      ENNReal.ofReal (finiteInformation μ p.prob) := by
  rw [p.law_fst μ,p.law_snd μ]
  let ν := μ.prod (p.outputLaw μ)
  let F := p.likelihoodRatio μ
  have he : p.law μ = ν.withDensity (fun x => ENNReal.ofReal (F x)) := p.law_eq_reference_density μ
  have : IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (F x))) := he ▸ p.law_probability μ
  rw [he,klDiv_withDensity_bounded ν F (p.measurable_likelihoodRatio μ)
    (p.likelihoodRatio_nonneg μ) (p.likelihoodRatio_le μ)]
  congr 1
  have hix := integrable_xlog_bounded ν F (p.measurable_likelihoodRatio μ)
    (p.likelihoodRatio_nonneg μ) (p.likelihoodRatio_le μ)
  rw [integral_prod_symm _ hix]
  change (∫ i,(∫ x,xlog (p.prob i x/scoreMass μ (p.prob i)) ∂μ) ∂p.outputLaw μ) = _
  rw [outputLaw,integral_withDensity_eq_integral_toReal_smul (measurable_of_countable _)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),integral_count]
  simp only [ENNReal.toReal_ofReal (scoreMass_nonneg μ _ (p.nonneg _)),smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => p.integral_xlog_ratio μ i)

end FiniteChannel

end RepeatedLocalization

end OAI
