import Mathlib
import OAI.Probability.Perceptron.Variational.QuantileReference
import OAI.Probability.Perceptron.Variational.CompactRestorationWitness
import OAI.Probability.Perceptron.Cascade.TwoVisitWeights

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem labelProfile_pair_reference_exists (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l,0<w l) (hw1 : ∑ l,w l=1) (q : Fin (k+1)→Time) (hq : Monotone q)
    (g : Jet3) (v v' : ℝ →ᵇ ℝ) (F : CompactOverlap →ᵇ ℝ) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f v v' F))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (∀ A : CompactOverlap →ᵇ ℝ,
        (∫ Q : CompactArray CompactJointOverlap, A (Q 0 1).1 ∂(ν : Measure _))=∑ l,w l*A (timeSpin (q l))) ∧
      (∀ j,(∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v v' F))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationPairMoment g.f v v' F j (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f v v' F))))=
        ∑ d,w d*F (timeSpin (q d))*
          (labelPairCoefficient k (stepCumulative w) (fun i => (q i:ℝ)) g
            (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) v d *
           labelPairCoefficient k (stepCumulative w) (fun i => (q i:ℝ)) g
            (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) v' d) := by
  let p := fun n => (Nat.unpair n).1
  let d := fun n => (Nat.unpair n).2
  have hcover : ∀ a b : ℕ, 1≤a+b → ∃ j,p j=a ∧ d j=b := by
    intro a b _
    exact ⟨Nat.pair a b,by simp [p,d]⟩
  obtain ⟨u,ρ,s,hu,hs,hlim,hGG,hex,hpair,hgeo⟩ := source_label_reference_exists k w hw hw1 p d hcover
  have hL := sourceGibbsArray_limit_label_geometry k 0 (fun _ j=>p j.val) (fun _ j=>d j.val)
    (fun _ _=>0) u (stepCumulative w) (fun _=>0) s hlim
  have hN := sourceGibbsArray_limit_label_nodes k 0 (fun _ j=>p j.val) (fun _ j=>d j.val)
    (fun _ _=>0) u (stepCumulative w) (fun _=>0) s hlim
  let ν := compactDiagonalMapLaw (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ
  obtain ⟨η,hm,hl⟩ := sourceLabelPair_witness k q hq 0 g v v' F
    (fun _ j=>p j.val) (fun _ j=>d j.val) (fun _ _=>0) (fun _ _=>le_rfl)
    (fun _=>monotone_const) u (stepCumulative w) (stepCumulative_strictMono w hw)
    (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1) (fun _=>0) s hlim
  refine ⟨ν,η,compactDiagonalMapLaw_gg _ _ _ _ ρ hGG,?_,?_,?_,?_⟩
  · change ∀ᵐ Q ∂(ρ : Measure (CompactArray CompactJointOverlap)).map
      (compactDiagonalMapArray (labelProfileMap q) labelProfileDiagonal), CompactSpinGeometry Q
    apply (ae_map_iff (compactDiagonalMapArray_continuous (labelProfileMap_continuous q) labelProfileDiagonal_continuous).measurable.aemeasurable
      compactSpinGeometry_closed.measurableSet).mpr
    filter_upwards [hL,hN] with Q hLQ hNQ
    exact labelProfileDiagonalMap_geometry q hq hLQ hNQ
  · intro A
    change (∫ Q : CompactArray CompactJointOverlap, A (Q 0 1).1
      ∂(compactDiagonalMapLaw (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ : Measure _))=_
    rw [compactDiagonalMapLaw_integral (labelProfileMap q) labelProfileDiagonal (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ
      (fun Q => A (Q 0 1).1) (by fun_prop)]
    have he : (∫ Q, A (labelProfileSpin q (Q 0 1).2) ∂(ρ : Measure (CompactArray CompactJointOverlap)))=
        ∫ Q, A (labelProfileSpin q (Q 1 0).2) ∂(ρ : Measure (CompactArray CompactJointOverlap)) := by
      apply integral_congr_ae
      filter_upwards [hL] with Q hLQ
      rw [show (Q 0 1).2=(Q 1 0).2 from Subtype.ext (hLQ.1 0 1)]
    change (∫ Q, A (labelProfileSpin q (Q 0 1).2) ∂(ρ : Measure (CompactArray CompactJointOverlap)))=_
    have hmap : (∫ x, A (labelProfileSpin q x) ∂((ρ : Measure (CompactArray CompactJointOverlap)).map
        (fun Q => (Q 1 0).2)))=∫ Q, A (labelProfileSpin q (Q 1 0).2)
          ∂(ρ : Measure (CompactArray CompactJointOverlap)) :=
      integral_map (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 1 0).2)
        from by fun_prop).aemeasurable
        (show Measurable (fun x : Time => A (labelProfileSpin q x)) from
          A.measurable.comp (labelProfileSpin_continuous q).measurable).aestronglyMeasurable
    rw [he,←hmap,hpair,sourceLabelLaw_integral k w (fun l => (hw l).le) (fun x => A (labelProfileSpin q x))
      (A.measurable.comp (labelProfileSpin_continuous q).measurable)]
    simp_rw [labelProfileSpin_node]
  · intro j
    rw [hm j]
    change _=∫ Q : CompactArray CompactJointOverlap,scalarRestorationPairMoment g.f v v' F j (fun i l => (Q i l).1.val)
      ∂(compactDiagonalMapLaw (labelProfileMap q) labelProfileDiagonal
        (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ : Measure _)
    rw [compactDiagonalMapLaw_integral (labelProfileMap q) labelProfileDiagonal
      (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ
      (fun Q => scalarRestorationPairMoment g.f v v' F j (fun i l => (Q i l).1.val))
      ((scalarRestorationPairMoment g.f v v' F j).continuous.comp (by fun_prop)).measurable]
    apply integral_congr_ae
    filter_upwards [hN] with Q hNQ
    exact (scalarRestorationPairMoment_diagonalMap q g.f v v' F j Q hNQ).symm
  · rw [hl]
    apply Finset.sum_congr rfl
    intro d _
    rw [twoVisitMass_stepCumulative w hw hw1]
    ring

lemma labelProfile_unmarked_reference_exists (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l,0<w l) (hw1 : ∑ l,w l=1) (q : Fin (k+1)→Time) (hq : Monotone q)
    (g : Jet3) (F : CompactOverlap →ᵇ ℝ) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (∀ A : CompactOverlap →ᵇ ℝ,
        (∫ Q : CompactArray CompactJointOverlap, A (Q 0 1).1 ∂(ν : Measure _))=∑ l,w l*A (timeSpin (q l))) ∧
      (∀ j,(∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationPairMoment g.f 1 1 F j (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=
        ∑ d,w d*F (timeSpin (q d)) := by
  obtain ⟨ν,η,hν,hgeo,hpair,hm,hl⟩ := labelProfile_pair_reference_exists k w hw hw1 q hq g 1 1 F
  refine ⟨ν,η,hν,hgeo,hpair,hm,?_⟩
  have h1 d := labelPairCoefficient_one k (stepCumulative w) (stepCumulative_pos w hw)
    (fun i => (q i:ℝ)) g (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) d
  simp_rw [h1] at hl
  simpa only [mul_one] using hl


theorem quantile_pair_reference_exists (q : Time→Time) (hq : Monotone q)
    (g : Jet3) (F : CompactOverlap →ᵇ ℝ) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
        (quantileSpinLaw q hq.measurable : Measure CompactOverlap) ∧
      (∀ j, (∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationPairMoment g.f 1 1 F j (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=
        ∫ z,F z ∂(quantileSpinLaw q hq.measurable : Measure CompactOverlap) := by
  have hex (n : ℕ) := labelProfile_unmarked_reference_exists n (fun _=>1/(n+1:ℝ))
    (by intro i; positivity) (uniformQuantileWeights_sum n) (uniformQuantileLower n q)
    (uniformQuantileLower_mono n hq) g F
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
  obtain ⟨η,-,t,ht,hη⟩ := isCompact_univ.isSeqCompact (fun n => mem_univ (ξ (s n)))
  have hv := hlim.comp ht.tendsto_atTop
  refine ⟨ν,η,hG,hgeom,hp,?_,?_⟩
  · intro j
    let A : WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F) →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨fun x => x.1.val*x.2.val^j,by fun_prop⟩
    let B : CompactArray CompactJointOverlap →ᵇ ℝ :=
      (scalarRestorationPairMoment g.f 1 1 F j).compContinuous
        ⟨fun Q i l => (Q i l).1.val,by fun_prop⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction A).continuousAt.tendsto.comp hη
    have h₂ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction B).continuousAt.tendsto.comp hv
    change Tendsto (fun n => ∫ x,x.1.val*x.2.val^j ∂(ξ (s (t n)) : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F)))) atTop
      (𝓝 (∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))) at h₁
    simp_rw [hm] at h₁
    exact tendsto_nhds_unique h₁ h₂
  · let A : WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F) →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨fun x => x.1.val*restorationReciprocal g.f 2 x.2,
        (continuous_subtype_val.comp continuous_fst).mul
          ((restorationReciprocal g.f 2).continuous.comp continuous_snd)⟩
    let B : CompactArray CompactJointOverlap →ᵇ ℝ := F.compContinuous ⟨fun Q => (Q 0 1).1,by fun_prop⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction A).continuousAt.tendsto.comp hη
    have h₂ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction B).continuousAt.tendsto.comp hv
    change Tendsto (fun n => ∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(ξ (s (t n)) : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F)))) atTop
      (𝓝 (∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))) at h₁
    simp_rw [hl,←hpair] at h₁
    have he := tendsto_nhds_unique h₁ h₂
    rw [he,←hp]
    exact (integral_map (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1)
      from by fun_prop).aemeasurable F.measurable.aestronglyMeasurable).symm

end SphericalPerceptronFreeEnergy
end

end OAI
