import Mathlib
import OAI.Probability.Perceptron.Cavity.FreshGGLogUniqueness
import OAI.Probability.Perceptron.Control.LabelProfileControl
import OAI.Probability.Perceptron.Variational.LabelProfileReferenceFull
import OAI.Probability.Perceptron.Control.QuantileControlTail

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma unit_pow_abs_sub_le (a b : Time) (r : ℕ) :
    |(a:ℝ)^r-(b:ℝ)^r|≤(r:ℝ)*|(a:ℝ)-b| := by
  have hm : max |(a:ℝ)| |(b:ℝ)|≤1 := by
    rw [abs_of_nonneg a.prop.1,abs_of_nonneg b.prop.1]
    exact max_le a.prop.2 b.prop.2
  have hp : max |(a:ℝ)| |(b:ℝ)|^(r-1)≤1 := pow_le_one₀ (by positivity) hm
  calc
    _ ≤ |(a:ℝ)-b| *r*max |(a:ℝ)| |(b:ℝ)|^(r-1) := abs_pow_sub_pow_le ..
    _ ≤ |(a:ℝ)-b| *r*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

lemma unit_pow_integrable {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    (q : A→Time) (hq : Measurable q) (r : ℕ) : Integrable (fun u => (q u:ℝ)^r) μ := by
  apply Integrable.of_bound ((measurable_subtype_coe.comp hq).pow_const r).aestronglyMeasurable 1
  exact ae_of_all _ fun u => by
    change ‖(q u:ℝ)^r‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (q u).prop.1 r)]
    exact pow_le_one₀ (q u).prop.1 (q u).prop.2

lemma sampleQuantileLower_moment_tendsto (q : Time→Time) (hq : Monotone q) (r : ℕ) :
    Tendsto (fun n => ∫ u, (sampleQuantileLower n q u:ℝ)^r ∂timeLaw) atTop
      (𝓝 (∫ u, (q u:ℝ)^r ∂timeLaw)) := by
  have hz : Tendsto (fun n : ℕ => (r:ℝ)*(1/(n+1:ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul (r:ℝ)
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hz
  rw [Real.dist_eq,←integral_sub (unit_pow_integrable timeLaw _ (sampleQuantileLower_mono n hq).measurable r)
    (unit_pow_integrable timeLaw q hq.measurable r)]
  calc
    _ ≤ ∫ u, |(sampleQuantileLower n q u:ℝ)^r-(q u:ℝ)^r| ∂timeLaw := by
      simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
        (fun u => (sampleQuantileLower n q u:ℝ)^r-(q u:ℝ)^r))
    _ ≤ ∫ u, (r:ℝ)*|(sampleQuantileLower n q u:ℝ)-q u| ∂timeLaw := by
      apply integral_mono
        ((unit_pow_integrable timeLaw _ (sampleQuantileLower_mono n hq).measurable r).sub
          (unit_pow_integrable timeLaw q hq.measurable r)).abs
        (((unit_valued_integrable timeLaw (sampleQuantileLower_mono n hq).measurable).sub
          (unit_valued_integrable timeLaw hq.measurable)).abs.const_mul (r:ℝ))
      exact fun u => unit_pow_abs_sub_le _ _ r
    _ = (r:ℝ)*∫ u, |(sampleQuantileLower n q u:ℝ)-q u| ∂timeLaw := integral_const_mul ..
    _ ≤ _ := mul_le_mul_of_nonneg_left (sampleQuantileLower_L1 n hq) (by positivity)

def quantileSpinLaw (q : Time→Time) (hq : Measurable q) : ProbabilityMeasure CompactOverlap :=
  ⟨timeLaw.map (fun u=>timeSpin (q u)),(Measure.isProbabilityMeasure_map_iff
    (timeSpin_continuous.measurable.comp hq).aemeasurable).2 inferInstance⟩

lemma quantileSpinLaw_integral (q : Time→Time) (hq : Measurable q)
    (F : CompactOverlap→ℝ) (hF : Measurable F) :
    (∫ x, F x ∂(quantileSpinLaw q hq : Measure CompactOverlap))=∫ u, F (timeSpin (q u)) ∂timeLaw :=
  integral_map (timeSpin_continuous.measurable.comp hq).aemeasurable hF.aestronglyMeasurable

theorem quantile_reference_exists (q : Time→Time) (hq : Monotone q) (g : Jet3)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (FreshPartitionRange g.f)),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
        (quantileSpinLaw q hq.measurable : Measure CompactOverlap) ∧
      (∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange g.f)))=
        ∫ Q, freshReplicaArrayKernel (expBCF 1 g.f) r Q ∂(ν : Measure _)) ∧
      (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange g.f)))=
        controlValue P g.f (quantileTrial q) := by
  have hex (n : ℕ) := labelProfile_reference_full_exists n (fun _=>1/(n+1:ℝ))
    (by intro i; positivity) (uniformQuantileWeights_sum n) (uniformQuantileLower n q)
    (uniformQuantileLower_mono n hq) g
  choose μ ξ hGG hgeo hpair hm hl using hex
  obtain ⟨ν,s,hs,hlim⟩ := compact_array_law_subsequence μ
  have hG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0 := by
    intro r i G a
    apply compactGGDefect_limit hlim r i G a
    simp only [Function.comp_apply,hGG]
    exact tendsto_const_nhds
  have hgeom : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q := by
    apply (mem_ae_iff_prob_eq_one compactSpinGeometry_closed.measurableSet).mpr
    have hv := weak_limit_closed_full hlim compactSpinGeometry_closed (fun n => ?_)
    · simp only [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]
    · have hh := (mem_ae_iff_prob_eq_one compactSpinGeometry_closed.measurableSet).mp (hgeo (s n))
      rw [←ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hh
      exact ENNReal.coe_injective hh
  have hp : (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
      (quantileSpinLaw q hq.measurable : Measure CompactOverlap) := by
    let ρ : ProbabilityMeasure CompactOverlap := ⟨(ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1),
      (Measure.isProbabilityMeasure_map_iff (show Measurable
        (fun array : CompactArray CompactJointOverlap => (array 0 1).1)
        from by fun_prop).aemeasurable).2 inferInstance⟩
    have he : ρ=quantileSpinLaw q hq.measurable := by
      apply probability_Icc_eq_of_moments
      intro r
      rw [quantileSpinLaw_integral q hq.measurable (fun x => x.val^r) (by fun_prop)]
      change (∫ x : CompactOverlap, x.val^r ∂(ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1))=_
      rw [integral_map (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1)
        from by fun_prop).aemeasurable (show Measurable (fun x : CompactOverlap => x.val^r) from by fun_prop).aestronglyMeasurable]
      let F : CompactOverlap→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x=>x.val^r,by fun_prop⟩
      let FF : CompactArray CompactJointOverlap→ᵇℝ := F.compContinuous ⟨fun Q => (Q 0 1).1,by fun_prop⟩
      have hν := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction FF).continuousAt.tendsto.comp hlim
      have hv n : (∫ Q, FF Q ∂(μ n : Measure _))=∫ u, (sampleQuantileLower n q u:ℝ)^r ∂timeLaw := by
        change (∫ Q, F (Q 0 1).1 ∂(μ n : Measure (CompactArray CompactJointOverlap)))=_
        rw [hpair n F]
        exact (uniformQuantileCell_integral n (fun i => (uniformQuantileLower n q i:ℝ)^r)).symm
      change Tendsto (fun n => ∫ Q, FF Q ∂(μ (s n) : Measure (CompactArray CompactJointOverlap))) atTop
        (𝓝 (∫ Q, FF Q ∂(ν : Measure (CompactArray CompactJointOverlap)))) at hν
      simp_rw [hv] at hν
      exact tendsto_nhds_unique hν ((sampleQuantileLower_moment_tendsto q hq r).comp hs.tendsto_atTop)
    exact congrArg (fun x : ProbabilityMeasure CompactOverlap => (x : Measure CompactOverlap)) he
  have hmom r : Tendsto (fun n => ∫ x, x.val^r ∂(ξ (s n) : Measure (FreshPartitionRange g.f))) atTop
      (𝓝 (∫ Q, freshReplicaArrayKernel (expBCF 1 g.f) r Q ∂(ν : Measure _))) := by
    simp_rw [hm]
    exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (freshReplicaArrayKernel (expBCF 1 g.f) r)).continuousAt.tendsto.comp hlim
  obtain ⟨η,hη,hηm⟩ := compact_moment_limit (fun n=>ξ (s n)) _ hmom
  refine ⟨ν,η,hG,hgeom,hp,hηm,?_⟩
  have hlog : Continuous (fun x : FreshPartitionRange g.f => Real.log x.val) :=
    continuous_subtype_val.log fun x => ne_of_gt ((Real.exp_pos _).trans_le x.prop.1)
  let F : FreshPartitionRange g.f→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨_,hlog⟩
  have hv := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).continuousAt.tendsto.comp hη
  have he n : (∫ x, F x ∂(ξ n : Measure (FreshPartitionRange g.f)))=
      controlValue P g.f (quantileTrial (sampleQuantileLower n q)) := by
    change (∫ x, Real.log x.val ∂(ξ n : Measure (FreshPartitionRange g.f)))=_
    rw [hl n,labelProfileValue_control n _ _ (uniformQuantileWeights_nonneg n) (uniformQuantileWeights_sum n)
      (uniformQuantileLower_mono n hq) g P hB]
    exact congrArg (controlValue P g.f) (sampleQuantile_trial n (uniformQuantileLower n q)).symm
  change Tendsto (fun n => ∫ x, F x ∂(ξ (s n) : Measure (FreshPartitionRange g.f))) atTop
    (𝓝 (∫ x, F x ∂(η : Measure (FreshPartitionRange g.f)))) at hv
  simp_rw [he] at hv
  have hc : Tendsto (fun n => controlValue P g.f (quantileTrial (sampleQuantileLower n q))) atTop
      (𝓝 (controlValue P g.f (quantileTrial q))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
      (show Tendsto (fun n : ℕ => (3/2:ℝ)*(‖g.d1‖₊:ℝ)^2*(1/(n+1:ℝ))) atTop (𝓝 0) from by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul ((3/2:ℝ)*(‖g.d1‖₊:ℝ)^2))
    exact (sampleQuantile_control_error P g q hq n).1
  exact tendsto_nhds_unique hv (hc.comp hs.tendsto_atTop)

end SphericalPerceptronFreeEnergy
end

end OAI
