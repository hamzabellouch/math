import Mathlib
import OAI.Probability.Perceptron.Cavity.ContinuousCavityProfile

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction BigOperators NNReal

lemma probabilityMap_tendsto_of_ae_tendsto {Ω X : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure Ω) (F : ℕ → Ω → X) (G : Ω → X)
    (hF : ∀ n, Measurable (F n)) (hG : Measurable G)
    (hlim : ∀ᵐ ω ∂(μ : Measure Ω), Tendsto (fun n => F n ω) atTop (𝓝 (G ω))) :
    Tendsto (fun n => μ.map (F n)) atTop (𝓝 (μ.map G)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have he n : (∫ x, f x ∂(μ.map (F n) : Measure X)) =
      ∫ ω, f (F n ω) ∂(μ : Measure Ω) :=
    integral_map (hF n).aemeasurable f.measurable.aestronglyMeasurable
  have hg : (∫ x, f x ∂(μ.map G : Measure X)) =
      ∫ ω, f (G ω) ∂(μ : Measure Ω) :=
    integral_map hG.aemeasurable f.measurable.aestronglyMeasurable
  simp_rw [he,hg]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    (fun n => (f.measurable.comp (hF n)).aestronglyMeasurable)
    (integrable_const _)
    (fun n => ae_of_all _ fun ω => f.norm_coe_le_norm _)
  exact hlim.mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω

lemma FiniteFieldModel.property_of_ae {f : Time→ℝ} (M : FiniteFieldModel f)
    (p : ℝ→Prop) (hf : ∀ᵐ u ∂timeLaw,p (f u)) (i : Fin (M.depth+1)) : p (M.value i) := by
  have hi : timeLaw (M.label ⁻¹' {i})≠0 := by
    intro hi
    have hp:=M.positive i
    change 0<(timeLaw (M.label ⁻¹' {i})).toReal at hp
    rw [hi] at hp
    simp at hp
  have hne : ∃ u,M.label u=i ∧ p (M.value (M.label u)) := by
    by_contra! hn
    have hz : ∀ᵐ u ∂timeLaw,u∉ M.label ⁻¹' {i} := by
      filter_upwards [M.agrees,hf] with u hu hv
      intro hm
      exact hn u hm (hu ▸ hv)
    exact hi (by simpa only [not_not,Set.ofPred_mem_eq] using ae_iff.mp hz)
  obtain ⟨u,hu,hv⟩:=hne
  simpa [hu] using hv

def quantileRoundLaw (η : Measure Time) [IsProbabilityMeasure η] (j : ℕ) : ProbabilityMeasure Time :=
  ProbabilityMeasure.map (⟨timeLaw,inferInstance⟩ : ProbabilityMeasure Time)
    (roundTime (unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)) j)

lemma quantileRoundLaw_tendsto (η : Measure Time) [IsProbabilityMeasure η] :
    Tendsto (quantileRoundLaw η) atTop (𝓝 (⟨η,inferInstance⟩ : ProbabilityMeasure Time)) := by
  have h:=probabilityMap_tendsto_of_ae_tendsto (⟨timeLaw,inferInstance⟩ : ProbabilityMeasure Time)
    (roundTime (unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)))
    (boundedQuantile η) (fun j=>(roundTime_mono _ j).measurable) (boundedQuantile_measurable η)
    (ae_of_all _ fun u=>roundTime_tendsto _ (boundedQuantile_monotone η) u)
  have he : ProbabilityMeasure.map (⟨timeLaw,inferInstance⟩ : ProbabilityMeasure Time) (boundedQuantile η)=
      (⟨η,inferInstance⟩ : ProbabilityMeasure Time) := by
    apply Subtype.ext
    exact boundedQuantile_law η
  rw [he] at h
  exact h

lemma realTail_quantileRoundLaw (η : Measure Time) [IsProbabilityMeasure η] (j : ℕ) (r : ℝ) :
    let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
    realTail (quantileRoundLaw η j) r=
      weightedStepTail (strictRoundModel F j).weight (fun i=>(roundTimeValue F j i:ℝ)) r := by
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  change (∫ x,1-max r (x:ℝ) ∂timeLaw.map (roundTime F j))=_
  rw [integral_map (roundTime_mono F j).measurable.aemeasurable (by fun_prop)]
  simpa only [F,roundTime,roundTimeValue,weightedStepTail,max_comm] using (strictRoundModel F j).integral (fun x=>1-max r x)

lemma quantileRoundLaw_support (η : Measure Time) [IsProbabilityMeasure η] {B : ℝ}
    (hη : ∀ᵐ r : Time ∂η,(r:ℝ)≤B) (j : ℕ) :
    ∀ᵐ r : Time ∂(quantileRoundLaw η j : Measure Time),(r:ℝ)≤B := by
  have hq : ∀ᵐ u ∂timeLaw,(boundedQuantile η u:ℝ)≤B := by
    have h:=hη
    rw [←boundedQuantile_law η] at h
    exact ae_of_ae_map (boundedQuantile_measurable η).aemeasurable h
  apply (ae_map_iff (roundTime_mono _ _).measurable.aemeasurable (measurableSet_le measurable_subtype_coe measurable_const)).mpr
  exact hq.mono fun u hu=>(roundLower_le j (boundedQuantile η u).prop.1).trans hu

lemma roundTimeValue_support (η : Measure Time) [IsProbabilityMeasure η] {B : ℝ}
    (hη : ∀ᵐ r : Time ∂η,(r:ℝ)≤B) (j : ℕ) :
    let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
    ∀ i,(roundTimeValue F j i:ℝ)≤B := by
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  have hq : ∀ᵐ u ∂timeLaw,(boundedQuantile η u:ℝ)≤B := by
    have h:=hη
    rw [←boundedQuantile_law η] at h
    exact ae_of_ae_map (boundedQuantile_measurable η).aemeasurable h
  exact (strictRoundModel F j).property_of_ae (fun r=>r≤B)
    (hq.mono fun u hu=>(roundLower_le j (boundedQuantile η u).prop.1).trans hu)

lemma cappedA_nonneg (η : Measure Time) [IsProbabilityMeasure η] (B : ℝ) {r : ℝ} (hr : 0≤r) :
    0≤cappedA η B r :=
  intervalIntegral.integral_nonneg hr (fun _ _=>sq_nonneg _)

lemma roundTimeValue_profile_exact (η : Measure Time) [IsProbabilityMeasure η]
    {B K a : ℝ} (hB : B<1) (ha0 : 0≤a) (haK : a≤K)
    (hA : ∀ᵐ r : Time ∂η,cappedA η B r≤a) (j : ℕ) :
    let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
    ∀ i,(continuousCavityProfile η B ha0 haK (roundTimeValue F j i)).2.val=
      cappedA η B (roundTimeValue F j i) := by
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  have hq : ∀ᵐ u ∂timeLaw,cappedA η B (boundedQuantile η u)≤a := by
    have h : ∀ᵐ r : Time ∂timeLaw.map (boundedQuantile η),cappedA η B r≤a := by
      have hl : timeLaw.map (boundedQuantile η)=η := boundedQuantile_law η
      rw [hl]
      exact hA
    exact ae_of_ae_map (boundedQuantile_measurable η).aemeasurable h
  have hv := (strictRoundModel F j).property_of_ae (fun r=>cappedA η B r≤a)
    (hq.mono fun u hu=>((cappedA_monotone η hB) (roundLower_le j (boundedQuantile η u).prop.1)).trans hu)
  dsimp only
  intro i
  change min a (max 0 (cappedA η B _))=_
  rw [max_eq_right (cappedA_nonneg η B (roundTimeValue F j i).prop.1)]
  exact min_eq_right (hv i)

lemma quantileRoundLaw_stationary (η : Measure Time) [IsProbabilityMeasure η] {B : ℝ}
    (hη : ∀ᵐ r : Time ∂η,(r:ℝ)≤B) (j : ℕ) :
    let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
    ∀ i,cappedA (quantileRoundLaw η j) B (roundTimeValue F j i)=
      weightedStepA (strictRoundModel F j).weight (fun l=>(roundTimeValue F j l:ℝ)) (roundTimeValue F j i) := by
  dsimp only
  intro i
  let F:=unitQuantileField (boundedQuantile η) (boundedQuantile_monotone η)
  rw [cappedA_eq_integral (quantileRoundLaw η j) (quantileRoundLaw_support η hη j)
    (roundTimeValue F j i).prop.1 (roundTimeValue_support η hη j i)]
  simp_rw [realTail_quantileRoundLaw]
  simp only [weightedStepA,one_div,inv_pow]
  rfl

end SphericalPerceptronFreeEnergy
end

end OAI
