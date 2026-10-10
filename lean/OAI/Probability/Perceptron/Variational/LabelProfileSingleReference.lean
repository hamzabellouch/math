import Mathlib
import OAI.Probability.Perceptron.Variational.QuantileReference
import OAI.Probability.Perceptron.Variational.RoundedMarkedSelection
import OAI.Probability.Perceptron.Variational.LabelSingleRestoredValue

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

theorem labelProfile_single_reference_exists (k : ℕ) (w : Fin (k+1)→ℝ)
    (hw : ∀ l,0<w l) (hw1 : ∑ l,w l=1) (q : Fin (k+1)→Time) (hq : Monotone q)
    (g : Jet3) (v v' : ℝ →ᵇ ℝ) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (∀ A : CompactOverlap →ᵇ ℝ,
        (∫ Q : CompactArray CompactJointOverlap, A (Q 0 1).1 ∂(ν : Measure _))=∑ l,w l*A (timeSpin (q l))) ∧
      (∀ j,(∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationSingleMoment g.f v v' j (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 1 x.2 ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))))=
        labelSingleCoefficient k (stepCumulative w) (fun i => (q i:ℝ)) g
          (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) v *
        labelSingleCoefficient k (stepCumulative w) (fun i => (q i:ℝ)) g
          (⟨1-q (Fin.last k),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩ : ℝ≥0) v'  := by
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
  obtain ⟨η,hm,hl⟩ := sourceLabelSingle_witness k q hq 0 g v v'
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
    change _=∫ Q : CompactArray CompactJointOverlap,scalarRestorationSingleMoment g.f v v' j (fun i l => (Q i l).1.val)
      ∂(compactDiagonalMapLaw (labelProfileMap q) labelProfileDiagonal
        (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ : Measure _)
    rw [compactDiagonalMapLaw_integral (labelProfileMap q) labelProfileDiagonal
      (labelProfileMap_continuous q) labelProfileDiagonal_continuous ρ
      (fun Q => scalarRestorationSingleMoment g.f v v' j (fun i l => (Q i l).1.val))
      ((scalarRestorationSingleMoment g.f v v' j).continuous.comp (by fun_prop)).measurable]
    apply integral_congr_ae
    filter_upwards [hN] with Q hNQ
    exact (scalarRestorationSingleMoment_diagonalMap q g.f v v' j Q hNQ).symm
  · exact hl

lemma rootPathMean_bound {X R : Type} [MeasurableSpace X] [MeasurableSpace R]
    (μ : Measure R) [IsProbabilityMeasure μ] (x : R→X) (n : ℕ) (κ : Fin n→Kernel X X)
    (hκ : ∀ i, IsMarkovKernel (κ i)) (f : X→ℝ) (C : ℝ) (hb : ∀ y,|f y|≤C) :
    |rootPathMean μ x n κ f|≤C := by
  simpa only [rootPathMean,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ:=μ)
      (f:=fun r => pathMean n κ f (x r))
      (ae_of_all _ fun r => by simpa only [Real.norm_eq_abs] using pathMean_bound n κ hκ f C hb (x r))

lemma labelSingleCoefficient_bound (k : ℕ) (z : Fin k→ℝ) (hz0 : ∀ i,0<z i)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) (v : ℝ →ᵇ ℝ) :
    |labelSingleCoefficient k z q g s v|≤‖v‖ := by
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)) : Measure (EuclideanSpace ℝ (Fin 1))) :=
    (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ (Fin 1))))
  have hI := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (labelGaussianStep q) (labelProfileTerminal_lipschitz g s) k z hz0
  have hκ i := cascadeTiltedStep_markov (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (gaussianLinearMarkStep (labelGaussianStep q)) (gaussianLinearMarkStep_measurable _)
    k z hz0 (fun x => labelProfileTerminal g s (x 0))
    ((labelProfileTerminal_lipschitz g s).continuous.measurable.comp (measurable_pi_apply 0)) hI.2 i
  exact rootPathMean_bound (stdGaussian (EuclideanSpace ℝ (Fin 1)))
    (fun r => fun _ => labelGaussianRoot q r) k _ hκ
    (fun x => labelResidualObservable s g.f v (x 0)) ‖v‖
    (fun x => labelResidualObservable_bound s g.f v (x 0))

lemma labelSingleCoefficient_one (k : ℕ) (z : Fin k→ℝ) (hz0 : ∀ i,0<z i)
    (q : Fin (k+1)→ℝ) (g : Jet3) (s : ℝ≥0) :
    labelSingleCoefficient k z q g s 1=1 := by
  let : IsGaussian (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)) : Measure (EuclideanSpace ℝ (Fin 1))) :=
    (inferInstance : IsGaussian (stdGaussian (EuclideanSpace ℝ (Fin 1))))
  have hI := gaussianLinearRecursion_realization (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (labelGaussianStep q) (labelProfileTerminal_lipschitz g s) k z hz0
  have hκ i := cascadeTiltedStep_markov (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin 1)))
    (gaussianLinearMarkStep (labelGaussianStep q)) (gaussianLinearMarkStep_measurable _)
    k z hz0 (fun x => labelProfileTerminal g s (x 0))
    ((labelProfileTerminal_lipschitz g s).continuous.measurable.comp (measurable_pi_apply 0)) hI.2 i
  have := pathOneKernel_markov k _ hκ
  simp only [labelSingleCoefficient,rootPathMean,labelResidualObservable,residualResponse_one,pathMean,
    integral_const,probReal_univ,one_smul]

def roundedSingleCoeff (q : BoundedField 1) (n : ℕ) (g : Jet3) (v : ℝ→ᵇℝ) : ℝ :=
  labelSingleCoefficient (strictRoundModel q n).depth (stepCumulative (strictRoundModel q n).weight)
    (strictRoundModel q n).value g
    ⟨1-roundTimeValue q n (Fin.last (strictRoundModel q n).depth),
      sub_nonneg.mpr (roundTimeValue q n _).prop.2⟩ v

lemma roundedSingleCoeff_bound (q : BoundedField 1) (n : ℕ) (g : Jet3) (v : ℝ→ᵇℝ) :
    |roundedSingleCoeff q n g v|≤‖v‖ :=
  labelSingleCoefficient_bound _ _ (stepCumulative_pos _ (strictRoundModel q n).weight_pos) _ _ _ _

lemma roundedSingleCoeff_one (q : BoundedField 1) (n : ℕ) (g : Jet3) :
    roundedSingleCoeff q n g 1=1 :=
  labelSingleCoefficient_one _ _ (stepCumulative_pos _ (strictRoundModel q n).weight_pos) _ _ _

theorem rounded_single_reference_exists (q : Time→Time) (hq : Monotone q)
    (g : Jet3) (v v' : ℝ→ᵇℝ)  (b : ℕ→ℕ) (hb : StrictMono b)
    (L : ℝ) (hL : Tendsto (fun n =>
      roundedSingleCoeff (unitQuantileField q hq) (b n) g v *
      roundedSingleCoeff (unitQuantileField q hq) (b n) g v') atTop (𝓝 L)) :
    ∃ (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
      (η : ProbabilityMeasure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))),
      (∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
        (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0) ∧
      (∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
      (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
        (quantileSpinLaw q hq.measurable : Measure CompactOverlap) ∧
      (∀ j,(∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))))=
        ∫ Q : CompactArray CompactJointOverlap,scalarRestorationSingleMoment g.f v v' j
          (fun i l => (Q i l).1.val) ∂(ν : Measure _)) ∧
      (∫ x,x.1.val*restorationReciprocal g.f 1 x.2
        ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))))=L := by
  have hex (n : ℕ) := labelProfile_single_reference_exists
    (strictRoundModel (unitQuantileField q hq) (b n)).depth
    (strictRoundModel (unitQuantileField q hq) (b n)).weight
    (strictRoundModel (unitQuantileField q hq) (b n)).weight_pos
    (strictRoundModel (unitQuantileField q hq) (b n)).weight_sum
    (roundTimeValue (unitQuantileField q hq) (b n)) (roundTimeValue_mono _ _) g v v'
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
      (Measure.isProbabilityMeasure_map_iff (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1)
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
    let A : WeightedRestorationRange g.f (singleRestorationBound g.f v v') →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨fun x => x.1.val*x.2.val^j,by fun_prop⟩
    let B : CompactArray CompactJointOverlap →ᵇ ℝ :=
      (scalarRestorationSingleMoment g.f v v' j).compContinuous
        ⟨fun Q i l => (Q i l).1.val,by fun_prop⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction A).continuousAt.tendsto.comp hη
    have h₂ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction B).continuousAt.tendsto.comp hv
    change Tendsto (fun n => ∫ x,x.1.val*x.2.val^j ∂(ξ (s (t n)) : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v')))) atTop
      (𝓝 (∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))))) at h₁
    simp_rw [hm] at h₁
    exact tendsto_nhds_unique h₁ h₂
  · let A : WeightedRestorationRange g.f (singleRestorationBound g.f v v') →ᵇ ℝ :=
      BoundedContinuousFunction.mkOfCompact ⟨fun x => x.1.val*restorationReciprocal g.f 1 x.2,
        (continuous_subtype_val.comp continuous_fst).mul
          ((restorationReciprocal g.f 1).continuous.comp continuous_snd)⟩
    have h₁ := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction A).continuousAt.tendsto.comp hη
    change Tendsto (fun n => ∫ x,x.1.val*restorationReciprocal g.f 1 x.2 ∂(ξ (s (t n)) : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v')))) atTop
      (𝓝 (∫ x,x.1.val*restorationReciprocal g.f 1 x.2 ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f v v'))))) at h₁
    simp_rw [hl] at h₁
    exact tendsto_nhds_unique h₁ (hL.comp (hs.comp ht).tendsto_atTop)

end SphericalPerceptronFreeEnergy
end

end OAI
