import Mathlib
import OAI.Probability.Perceptron.Variational.LabelProfilePairReference
import OAI.Probability.Perceptron.Variational.RoundedMarkedSelection

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

theorem rounded_marked_reference_exists (q : Time→Time) (hq : Monotone q)
    (g : Jet3) (v v' : ℝ→ᵇℝ) (F : CompactOverlap→ᵇℝ) (b : ℕ→ℕ) (hb : StrictMono b)
    (L : ℝ) (hL : Tendsto (fun n => ∑ i,(strictRoundModel (unitQuantileField q hq) (b n)).weight i*
      F (timeSpin (roundTimeValue (unitQuantileField q hq) (b n) i))*
        (roundedPairCoeff (unitQuantileField q hq) (b n) g v i *
         roundedPairCoeff (unitQuantileField q hq) (b n) g v' i)) atTop (𝓝 L)) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f v v' F))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
        (quantileSpinLaw q hq.measurable : Measure CompactOverlap) ∧
      (∀ j,(∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v v' F))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationPairMoment g.f v v' F j
          (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 2 x.2
        ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v v' F))))=L := by
  have hex (n : ℕ) := labelProfile_pair_reference_exists
    (strictRoundModel (unitQuantileField q hq) (b n)).depth
    (strictRoundModel (unitQuantileField q hq) (b n)).weight
    (strictRoundModel (unitQuantileField q hq) (b n)).weight_pos
    (strictRoundModel (unitQuantileField q hq) (b n)).weight_sum
    (roundTimeValue (unitQuantileField q hq) (b n)) (roundTimeValue_mono _ _) g v v' F
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
      let A : CompactOverlap→ᵇℝ := BoundedContinuousFunction.mkOfCompact ⟨fun x=>x.val^r,by fun_prop⟩
      let B : CompactArray CompactJointOverlap→ᵇℝ := A.compContinuous ⟨fun Q => (Q 0 1).1,by fun_prop⟩
      have hν := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction B).continuousAt.tendsto.comp hlim
      change Tendsto (fun n => ∫ Q, A (Q 0 1).1 ∂(μ (s n) : Measure (CompactArray CompactJointOverlap))) atTop
        (𝓝 (∫ Q, (Q 0 1).1.val^r ∂(ν : Measure (CompactArray CompactJointOverlap)))) at hν
      simp_rw [hpair] at hν
      exact tendsto_nhds_unique hν
        ((roundTime_sum_tendsto q hq A).comp (hb.comp hs).tendsto_atTop)
    exact congrArg (fun x : ProbabilityMeasure CompactOverlap => (x : Measure CompactOverlap)) he
  obtain ⟨η,-,t,ht,hη⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (ξ (s n)))
  have hv := hlim.comp ht.tendsto_atTop
  refine ⟨ν,η,hG,hgeom,hp,?_,?_⟩
  · intro j
    let A : WeightedRestorationRange g.f (pairRestorationBound g.f v v' F) →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨fun x => x.1.val*x.2.val^j,by fun_prop⟩
    let B : CompactArray CompactJointOverlap →ᵇ ℝ :=
      (scalarRestorationPairMoment g.f v v' F j).compContinuous
        ⟨fun Q i l => (Q i l).1.val,by fun_prop⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction A).continuousAt.tendsto.comp hη
    have h₂ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction B).continuousAt.tendsto.comp hv
    change Tendsto (fun n => ∫ x,x.1.val*x.2.val^j ∂(ξ (s (t n)) : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v v' F)))) atTop
      (𝓝 (∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v v' F))))) at h₁
    simp_rw [hm] at h₁
    exact tendsto_nhds_unique h₁ h₂
  · let A : WeightedRestorationRange g.f (pairRestorationBound g.f v v' F) →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨fun x => x.1.val*restorationReciprocal g.f 2 x.2,
        (continuous_subtype_val.comp continuous_fst).mul
          ((restorationReciprocal g.f 2).continuous.comp continuous_snd)⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction A).continuousAt.tendsto.comp hη
    change Tendsto (fun n => ∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(ξ (s (t n)) : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v v' F)))) atTop
      (𝓝 (∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v v' F))))) at h₁
    simp_rw [hl] at h₁
    exact tendsto_nhds_unique h₁ (hL.comp (hs.comp ht).tendsto_atTop)

def secondPairMark (v : ℝ→ᵇℝ) (b : Bool) : ℝ→ᵇℝ := if b then v else 1

def pairMarkPower (b : Bool) : ℕ := if b then 2 else 1

lemma roundedPairCoeff_one (q : BoundedField 1) (n : ℕ) (g : Jet3) (i : Fin ((strictRoundModel q n).depth+1)) :
    roundedPairCoeff q n g 1 i=1 :=
  labelPairCoefficient_one _ _ (stepCumulative_pos _ (strictRoundModel q n).weight_pos) _ _ _ _

lemma roundedPair_mark_tendsto (q : Time→Time) (hq : Monotone q) (g : Jet3) (v : ℝ→ᵇℝ)
    (s : ℕ→ℕ) (hs : StrictMono s) (a : ℝ→ℝ)
    (ha : ∀ r,Tendsto (fun n => roundedPairFunction (unitQuantileField q hq) (s n) g v r)
      atTop (𝓝 (a r))) (F : CompactOverlap→ᵇℝ) (b : Bool) :
    Tendsto (fun n => ∑ i,(strictRoundModel (unitQuantileField q hq) (s n)).weight i*
      F (timeSpin (roundTimeValue (unitQuantileField q hq) (s n) i))*
        (roundedPairCoeff (unitQuantileField q hq) (s n) g v i *
         roundedPairCoeff (unitQuantileField q hq) (s n) g (secondPairMark v b) i)) atTop
      (𝓝 (∫ u,F (timeSpin (q u))*(a (q u))^(pairMarkPower b) ∂timeLaw)) := by
  have h := roundedPair_sum_tendsto q hq g v s hs a ha F (pairMarkPower b)
  cases b
  · simpa only [secondPairMark,pairMarkPower,Bool.false_eq_true,ite_false,roundedPairCoeff_one,pow_one,mul_one] using h
  · simpa only [secondPairMark,pairMarkPower,ite_true,pow_two] using h

theorem quantile_marked_pair_reference_exists (q : Time→Time) (hq : Monotone q)
    (g : Jet3) (v : ℝ→ᵇℝ) : ∃ a : ℝ→ℝ, Monotone a ∧ (∀ r,0≤a r ∧ a r≤‖v‖^2) ∧
      ∀ (F : CompactOverlap→ᵇℝ) (b : Bool),
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f v (secondPairMark v b) F))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
        (quantileSpinLaw q hq.measurable : Measure CompactOverlap) ∧
      (∀ j,(∫ x,x.1.val*x.2.val^j
        ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v (secondPairMark v b) F))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationPairMoment g.f v (secondPairMark v b) F j
          (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 2 x.2
        ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v (secondPairMark v b) F))))=
          ∫ u,F (timeSpin (q u))*(a (q u))^(pairMarkPower b) ∂timeLaw := by
  obtain ⟨s,a,hs,ham,hab,hal⟩ := roundedPair_selection (unitQuantileField q hq) g v
  refine ⟨a,ham,hab,fun F b => ?_⟩
  exact rounded_marked_reference_exists q hq g v (secondPairMark v b) F s hs _
    (roundedPair_mark_tendsto q hq g v s hs a hal F b)

end SphericalPerceptronFreeEnergy
end

end OAI
