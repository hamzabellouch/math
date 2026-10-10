import Mathlib
import OAI.Probability.Ballisticity.Geometry.WindowProjection
import OAI.Probability.Ballisticity.Estimates.IndependentDyadic

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

abbrev CurrentData {d : ℕ} (e : Direction d) := ReferenceClasses.Data (HorizontalSpace e) × CurrentProfiles e

def currentDust {d : ℕ} (e : Direction d) (A : CurrentData e) (a : ℕ) : Prop := (A.2 (a,0):ℝ)=0

lemma currentDust_measurable {d : ℕ} (e : Direction d) (a : ℕ) :
    MeasurableSet {A : CurrentData e | currentDust e A a} := by
  exact (((measurable_pi_apply (a,0)).comp measurable_snd).subtype_val) (measurableSet_singleton 0)

noncomputable def currentDustFrequency {d : ℕ} (e : Direction d) (n : ℕ) (A : CurrentData e) : ℝ :=
  ReferenceClasses.dustFrequency (currentDust e A) n

lemma currentDustFrequency_measurable {d : ℕ} (e : Direction d) (n : ℕ) :
    Measurable (currentDustFrequency e n) := by
  unfold currentDustFrequency ReferenceClasses.dustFrequency
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro a _
  exact Measurable.ite (currentDust_measurable e a) measurable_const measurable_const

noncomputable def currentDustWeight {d : ℕ} (e : Direction d) (n : ℕ) (W : CurrentWindow e) : ℝ :=
  ReferenceClasses.dustWeight (currentDust e W.1) (fun ξ => (upperNoDrop e ξ).toReal) n W.2

lemma currentDustWeight_measurable {d : ℕ} (e : Direction d) (n : ℕ) :
    Measurable (currentDustWeight e n) := by
  unfold currentDustWeight ReferenceClasses.dustWeight sampleAverage
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro a _
  exact Measurable.ite ((currentDust_measurable e a).preimage measurable_fst)
    ((upperNoDrop_measurable e).ennreal_toReal.comp (Measurable.of_eval fun position =>
      (measurable_pi_apply (a,position)).comp measurable_snd)) measurable_const

noncomputable def upperNoDropMean {d : ℕ} (e : Direction d) (ν : Measure (Row d)) : ℝ :=
  ∫ ξ, (upperNoDrop e ξ).toReal ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)

lemma upperNoDrop_toReal_bound {d : ℕ} (e : Direction d) (ξ : UpperRows e) :
    |(upperNoDrop e ξ).toReal|≤1 := by
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono ENNReal.one_ne_top (upperNoDrop_le_one e ξ)).trans_eq ENNReal.toReal_one

lemma upperNoDropMean_pos {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (htrans : DirectionallyTransient ν (realPosition (step e))) :
    0<upperNoDropMean e ν := by
  have hi : Integrable (fun ξ => (upperNoDrop e ξ).toReal)
      (Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)) :=
    (integrable_const (1:ℝ)).mono' (upperNoDrop_measurable e).ennreal_toReal.aestronglyMeasurable
      (Eventually.of_forall (upperNoDrop_toReal_bound e))
  by_contra hh
  have hz : (∫ ξ, (upperNoDrop e ξ).toReal ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν))=0 :=
    le_antisymm (le_of_not_gt hh) (integral_nonneg fun _ => ENNReal.toReal_nonneg)
  have he := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hi).mp hz
  obtain ⟨ξ,hp,hz⟩ := ((upperNoDrop_positive_ae e ν hue htrans).and he).exists
  exact (ENNReal.toReal_pos hp.ne' (ne_top_of_le_ne_top ENNReal.one_ne_top (upperNoDrop_le_one e ξ))).ne' hz

lemma current_reference_dust_law {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (W : Measure (CurrentWindow e)) [IsProbabilityMeasure W]
    (hisolated : ∀ᵐ A ∂W.fst, ∀ a, currentDust e A a → ∀ b,
      ReferenceClasses.related A.1 a b → a=b)
    (hentropy : klDiv W (W.fst.compProd (currentWindowReference e ν))≠⊤) :
    ∀ᵐ w ∂W, Tendsto (fun r : ℕ => currentDustWeight e (2^r) w-
      upperNoDropMean e ν*currentDustFrequency e (2^r) w.1) atTop (𝓝 0) := by
  apply (klDiv_ne_top_iff.mp hentropy).1.ae_le
  apply (Measure.ae_compProd_iff (measurableSet_tendsto (𝓝 (0:ℝ)) (fun r =>
    (currentDustWeight_measurable e (2^r)).sub
      (((currentDustFrequency_measurable e (2^r)).comp measurable_fst).const_mul _)))).mpr
  filter_upwards [hisolated] with A hA
  exact ReferenceClasses.reference_dust_dyadic ν A.1 (currentDust e A) hA
    (fun ξ => (upperNoDrop e ξ).toReal) (upperNoDrop_measurable e).ennreal_toReal
      (upperNoDrop_toReal_bound e)

lemma reference_ae_fields {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (O : ReferenceClasses.Data (HorizontalSpace e)) (P : UpperRows e → Prop)
    (hP : MeasurableSet {ξ | P ξ})
    (hp : ∀ᵐ ξ ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν), P ξ) :
    ∀ᵐ φ ∂ ReferenceClasses.reference ν O, ∀ a : ℕ, P (fun p => φ (a,p)) := by
  apply ae_all_iff.mpr
  intro a
  rw [←ReferenceClasses.reference_single_field ν O a] at hp
  exact (ae_map_iff (Measurable.of_eval (fun position =>
    measurable_pi_apply (a,position))).aemeasurable hP).mp hp

lemma current_reference_nodrop_le {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (W : Measure (CurrentWindow e)) [IsProbabilityMeasure W]
    (hentropy : klDiv W (W.fst.compProd (currentWindowReference e ν))≠⊤) :
    ∀ᵐ w ∂W, ∀ a H : ℕ, upperNoDrop e (fun p => w.2 (a,p))≤
      upperHorizontalKernel e H (fun p => w.2 (a,p)) 0 Set.univ := by
  have hm : MeasurableSet {ξ : UpperRows e | ∀ H : ℕ,
      upperNoDrop e ξ≤upperHorizontalKernel e H ξ 0 Set.univ} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun H => measurableSet_le (upperNoDrop_measurable e)
      (upperHorizontalKernel_lowerSemicontinuous e H 0 Set.univ).measurable
  apply (klDiv_ne_top_iff.mp hentropy).1.ae_le
  apply (Measure.ae_compProd_iff (by
    simp only [Set.ofPred_forall]
    refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun H => ?_
    have heval : Measurable (fun w : CurrentWindow e => fun p => w.2 (a,p)) :=
      Measurable.of_eval fun position => (measurable_pi_apply (a,position)).comp measurable_snd
    exact measurableSet_le ((upperNoDrop_measurable e).comp heval)
      ((upperHorizontalKernel_lowerSemicontinuous e H 0 Set.univ).measurable.comp heval))).mpr
  exact Eventually.of_forall fun A => reference_ae_fields e ν A.1 _ hm (upperNoDrop_le_kernel_ae e ν htrans)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma average_zero_of_survival (p : ℝ) (hp : 0<p) (D : ℕ → ℝ)
    (hD : ∀ r, 0≤D r) (S W : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (hS : ∀ m, IsBoundedUnder (·≤·) atTop (S m))
    (hWS : ∀ m r, W m r≤S m r)
    (hcenter : ∀ m, Tendsto (fun r => W m r-p*D r) atTop (𝓝 0))
    (hlim : ∀ m, limsup (S m) atTop≤a m)
    (hz : ∀ ε : ℝ, 0<ε → ∃ m, a m<ε) : Tendsto D atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨m,hm⟩ := hz (p*ε/2) (by positivity)
  have hsev := eventually_lt_of_limsup_lt ((hlim m).trans_lt hm) (hS m)
  have hwev := (tendsto_order.mp (hcenter m)).1 (-p*ε/2) (by nlinarith)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hsev.and hwev)
  refine ⟨N,fun r hr => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hD r)]
  have hh := hN r hr
  have hw := hWS m r
  nlinarith

lemma symmetric_indicator_zero_of_average {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (I : ℕ → Ω → ℝ)
    (hI : ∀ a, Measurable (I a)) (hb : ∀ a ω, I a ω∈Set.Icc 0 1)
    (hmean : ∀ a, (∫ ω, I a ω ∂μ)=∫ ω, I 0 ω ∂μ)
    (ns : ℕ → ℕ) (hn : ∀ r, 0<ns r)
    (hz : ∀ᵐ ω ∂μ, Tendsto (fun r => (ns r:ℝ)⁻¹*∑ a∈Finset.range (ns r), I a ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ a, I a ω=0 := by
  have hi (a : ℕ) : Integrable (I a) μ :=
    (memLp_of_bounded (Eventually.of_forall (hb a)) (hI a).aestronglyMeasurable 1).integrable (by rfl)
  let F : ℕ → Ω → ℝ := fun r ω => (ns r:ℝ)⁻¹*∑ a∈Finset.range (ns r), I a ω
  have hf (r : ℕ) (ω : Ω) : F r ω∈Set.Icc 0 1 := by
    refine ⟨mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => (hb a ω).1),?_⟩
    calc F r ω ≤ (ns r:ℝ)⁻¹*∑ _a∈Finset.range (ns r), (1:ℝ) :=
           mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => (hb a ω).2) (by positivity)
         _ = 1 := by simp [(hn r).ne']
  have he (r : ℕ) : (∫ ω, F r ω ∂μ)=∫ ω, I 0 ω ∂μ := by
    dsimp only [F]
    rw [integral_const_mul,integral_finsetSum _ (fun a _ => hi a)]
    simp only [hmean,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast (hn r).ne'),one_mul]
  have hl := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1:ℝ))
    (fun r => (show Measurable (F r) from by dsimp [F]; fun_prop).aestronglyMeasurable)
    (integrable_const 1) (fun r => Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hf r ω).1]; exact (hf r ω).2) hz
  simp only [he,integral_zero] at hl
  have hzero : (∫ ω, I 0 ω ∂μ)=0 := tendsto_nhds_unique tendsto_const_nhds hl
  apply ae_all_iff.mpr
  intro a
  exact (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun ω => (hb a ω).1) (hi a)).mp
    ((hmean a).trans hzero)

end DirectionalTransience

end

end OAI
