import Mathlib
import OAI.Probability.Ballisticity.Estimates.RecordMedianSlope
import OAI.Probability.Ballisticity.Walk.RecordLinearPath

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma sharedConditionedPairLaw_fst {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (y : Lattice d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) :
    (sharedConditionedPairLaw ν ℓ 0 y).map Prod.fst =
      normalizedMeasure (weightedConditioned ν ℓ (noDropQuenched ℓ y)) := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA,sharedConditionedPairLaw,Measure.smul_apply,
    Measure.restrict_apply (hA.preimage measurable_fst)]
  have he : Prod.fst ⁻¹' A ∩ (NoDrop ℓ 0 ×ˢ NoDrop ℓ y) =
      (A ∩ NoDrop ℓ 0) ×ˢ NoDrop ℓ y := by ext Z; exact and_assoc.symm
  rw [he,sharedPairLaw_rectangle ν 0 y _ _ (hA.inter (measurableSet_noDrop ℓ 0))
    (measurableSet_noDrop ℓ y),normalizedMeasure,Measure.smul_apply,
    weightedConditioned_noDrop_mass,weightedConditioned_apply ν ℓ _ (measurable_noDropQuenched ℓ y) A hA]
  simp only [smul_eq_mul]
  have hc : (((annealedLaw ν (NoDrop ℓ 0))⁻¹ * sharedNoDropMass ν ℓ 0 y)⁻¹ *
      (annealedLaw ν (NoDrop ℓ 0))⁻¹) = (sharedNoDropMass ν ℓ 0 y)⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)))
      (Or.inl (ENNReal.inv_ne_top.mpr hp)),inv_inv,mul_right_comm,
      ENNReal.mul_inv_cancel hp (measure_ne_top _ _),one_mul]
  rw [← mul_assoc,hc]
  congr 1
  apply lintegral_congr
  intro ω
  exact mul_comm _ _

lemma sharedPairLaw_swap {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (x y : Lattice d) : (sharedPairLaw ν x y).map Prod.swap = sharedPairLaw ν y x := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply measurable_swap (hA.prod hB)]
  have he : Prod.swap ⁻¹' (A ×ˢ B) = B ×ˢ A := by ext Z; exact and_comm
  rw [he,sharedPairLaw_rectangle ν x y B A hB hA,sharedPairLaw_rectangle ν y x A B hA hB]
  apply lintegral_congr
  intro ω
  exact mul_comm _ _

lemma sharedNoDropMass_swap {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (x y : Lattice d) : sharedNoDropMass ν ℓ x y = sharedNoDropMass ν ℓ y x := by
  unfold sharedNoDropMass
  apply lintegral_congr
  intro ω
  exact mul_comm _ _

lemma sharedConditionedPairLaw_swap {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) :
    (sharedConditionedPairLaw ν ℓ x y).map Prod.swap = sharedConditionedPairLaw ν ℓ y x := by
  have he : Prod.swap ⁻¹' (NoDrop ℓ y ×ˢ NoDrop ℓ x) = NoDrop ℓ x ×ˢ NoDrop ℓ y := by
    ext Z; exact and_comm
  rw [sharedConditionedPairLaw,Measure.map_smul _ measurable_swap.aemeasurable,← he,← Measure.restrict_map measurable_swap
    ((measurableSet_noDrop ℓ y).prod (measurableSet_noDrop ℓ x)),sharedPairLaw_swap,
    sharedNoDropMass_swap]
  rfl

lemma sharedPairLaw_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (z x y : Lattice d) :
    (sharedPairLaw ν (z+x) (z+y)).map
      (fun Z : Path d × Path d => ((fun j => Z.1 j-z),(fun j => Z.2 j-z))) = sharedPairLaw ν x y := by
  have hm : Measurable (fun X : Path d => fun j => X j-z) := by fun_prop
  have hpair : Measurable (fun Z : Path d × Path d => ((fun j => Z.1 j-z),(fun j => Z.2 j-z))) := by fun_prop
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply hpair (hA.prod hB)]
  have he : (fun Z : Path d × Path d => ((fun j => Z.1 j-z),(fun j => Z.2 j-z))) ⁻¹' (A ×ˢ B) =
      ((fun X : Path d => fun j => X j-z) ⁻¹' A) ×ˢ ((fun X : Path d => fun j => X j-z) ⁻¹' B) := rfl
  rw [he,sharedPairLaw_rectangle ν (z+x) (z+y) _ _ (hA.preimage hm) (hB.preimage hm),
    sharedPairLaw_rectangle ν x y A B hA hB]
  have ht (ω : Environment d) (a : Lattice d) (C : Set (Path d)) (hC : MeasurableSet C) :
      quenchedKernel (ω,z+a) ((fun X : Path d => fun j => X j-z) ⁻¹' C) =
        quenchedKernel ((fun b => ω (z+b)),a) C := by
    rw [← Measure.map_apply hm hC,quenched_translation]
  simp_rw [ht _ x A hA,ht _ y B hB]
  have henv : Measurable (fun ω : Environment d => fun b => ω (z+b)) := by fun_prop
  have hprod : Measurable (fun ω : Environment d => quenchedKernel (ω,x) A * quenchedKernel (ω,y) B) :=
    ((Kernel.measurable_coe _ hA).comp (measurable_id.prodMk measurable_const)).mul
      ((Kernel.measurable_coe _ hB).comp (measurable_id.prodMk measurable_const))
  rw [← lintegral_map hprod henv,environment_translation]

lemma sharedNoDropMass_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (z x y : Lattice d) :
    sharedNoDropMass ν ℓ (z+x) (z+y) = sharedNoDropMass ν ℓ x y := by
  rw [sharedNoDropMass_eq,sharedNoDropMass_eq,← sharedPairLaw_translation ν z x y,
    Measure.map_apply (by fun_prop) ((measurableSet_noDrop ℓ x).prod (measurableSet_noDrop ℓ y))]
  congr 1
  change NoDrop ℓ (z+x) ×ˢ NoDrop ℓ (z+y) =
    ((fun X : Path d => fun j => X j-z) ⁻¹' NoDrop ℓ x) ×ˢ
      ((fun X : Path d => fun j => X j-z) ⁻¹' NoDrop ℓ y)
  rw [noDrop_translation,noDrop_translation]

lemma sharedConditionedPairLaw_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (z x y : Lattice d) :
    (sharedConditionedPairLaw ν ℓ (z+x) (z+y)).map
      (fun Z : Path d × Path d => ((fun j => Z.1 j-z),(fun j => Z.2 j-z))) =
        sharedConditionedPairLaw ν ℓ x y := by
  have hm : Measurable (fun Z : Path d × Path d => ((fun j => Z.1 j-z),(fun j => Z.2 j-z))) := by fun_prop
  have he : (fun Z : Path d × Path d => ((fun j => Z.1 j-z),(fun j => Z.2 j-z))) ⁻¹'
      (NoDrop ℓ x ×ˢ NoDrop ℓ y) = NoDrop ℓ (z+x) ×ˢ NoDrop ℓ (z+y) := by
    change ((fun X : Path d => fun j => X j-z) ⁻¹' NoDrop ℓ x) ×ˢ
      ((fun X : Path d => fun j => X j-z) ⁻¹' NoDrop ℓ y) = _
    rw [noDrop_translation,noDrop_translation]
  rw [sharedConditionedPairLaw,Measure.map_smul _ hm.aemeasurable,← he,← Measure.restrict_map hm
      ((measurableSet_noDrop ℓ x).prod (measurableSet_noDrop ℓ y)),sharedPairLaw_translation,
      sharedNoDropMass_translation]
  rfl

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma tendstoInDistribution_pullback {Ω Ω' E E' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace E'] [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] (μ : ℕ → Measure Ω) (η : ℕ → Measure Ω')
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (η i)]
    (S : ℕ → Ω → Ω') (hS : ∀ i, Measurable (S i)) (hm : ∀ i, (μ i).map (S i) = η i)
    (F : ℕ → Ω' → E) (hF : ∀ i, Measurable (F i)) (G : E' → E)
    (W : Measure E') [IsProbabilityMeasure W]
    (hlim : TendstoInDistribution F atTop G η W) :
    TendstoInDistribution (fun i => F i ∘ S i) atTop G μ W := by
  refine ⟨fun i => ((hF i).comp (hS i)).aemeasurable,hlim.aemeasurable_limit,?_⟩
  apply hlim.tendsto.congr'
  apply Eventually.of_forall
  intro i
  apply Subtype.ext
  change (η i).map (F i) = (μ i).map (F i ∘ S i)
  rw [← Measure.map_map (hF i) (hS i),hm]

lemma sharedNoDropMass_pos {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d) :
    0 < sharedNoDropMass ν ℓ x y := by
  obtain ⟨c,hc,hm⟩ := sharedNoDropMass_uniform_positive ν hue ℓ hℓ htrans
  exact hc.trans_le (hm x y)

lemma distribution_sequence_tight {Ω E Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : ℕ → Ω → E) (G : Ω' → E) (W : Measure Ω') [IsProbabilityMeasure W]
    (h : TendstoInDistribution X atTop G μ W) :
    IsTightMeasureSet (Set.range (fun i => (μ i).map (X i))) := by
  let A : ℕ → ProbabilityMeasure E := fun i => ⟨(μ i).map (X i), inferInstance⟩
  let B : ProbabilityMeasure E := ⟨W.map G, inferInstance⟩
  have hh : Tendsto A atTop (𝓝 B) := h.tendsto
  have ht := weak_sequence_tight (E := E) (μ := A) (ν := B) hh
  exact ht

theorem shared_first_zero_path_limit {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      (∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
        (fun g : C(unitInterval,ℝ) => I.restrict g) =
          gaussianPathFiniteLaw (T/(2*commonMeanWidth ν ℓ)) I) ∧
      ∀ y : ℕ → Lattice d, (∀ i, signedHeight e (y i) = 0) →
        letI : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ 0 (y i)) := fun i =>
          sharedConditionedPairLaw_probability ν ℓ 0 (y i)
            (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans 0 (y i)))
        TendstoInDistribution (fun i Z => recordLinearPath ℓ f
          (recordMedianSlope ν ℓ hp f (r i)) (r i)
          (fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)) T Z.1)
          atTop id (fun i => sharedConditionedPairLaw ν ℓ 0 (y i)) W := by
  let ℓ := realPosition (step e)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let θ i := recordMedianSlope ν ℓ hp f (r i)
  let n i := fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  obtain ⟨W,hW,hWf⟩ := transverse_firstHit_linear_path_limit ν hue e f hef htrans r hr hT
  obtain ⟨W',hW',_⟩ := transverse_firstHit_linear_path_limit ν hue e f hef htrans r hr (show 0 ≤ T+1 by linarith)
  have ht : IsTightMeasureSet (Set.range (fun i => (conditionedLaw ν ℓ).map
      (recordLinearPath ℓ f (θ i) (r i) (n i) (T+1)))) := by
    have hh := distribution_sequence_tight _ _ _ _ hW'
    change IsTightMeasureSet (Set.range (fun i => (conditionedLaw ν ℓ).map
      (fun X => heightPolygon (fun h => signedCoordinate f (recordIndexPosition ℓ h X)-
        (h:ℝ)*θ i) (r i) (n i) (T+1))))
    exact hh
  refine ⟨W,hWf,?_⟩
  intro y hy
  let : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ 0 (y i)) := fun i =>
    sharedConditionedPairLaw_probability ν ℓ 0 (y i)
      (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans 0 (y i)))
  obtain ⟨c₀,hc₀,hc₀m⟩ := sharedNoDropMass_uniform_positive ν hue ℓ (signed_direction_unit e) htrans
  let c := (annealedLaw ν (NoDrop ℓ 0))⁻¹*c₀
  have hc : 0 < c := ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) hc₀.ne'
  have hcmass (i : ℕ) : c ≤ weightedConditioned ν ℓ (noDropQuenched ℓ (y i)) Set.univ := by
    rw [weightedConditioned_noDrop_mass]
    exact mul_le_mul_right (hc₀m 0 (y i)) _
  let μ i := normalizedMeasure (weightedConditioned ν ℓ (noDropQuenched ℓ (y i)))
  let : ∀ i, IsFiniteMeasure (weightedConditioned ν ℓ (noDropQuenched ℓ (y i))) := fun i =>
    weightedConditioned_finite ν ℓ _ (measurable_noDropQuenched ℓ (y i)) (fun _ => prob_le_one)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => normalizedMeasure_probability _
    (ne_of_gt (hc.trans_le (hcmass i)))
  have hlim := noDropWeighted_recordLinearPath_limit ν e f htrans θ r n hr.1
    (recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1)
    (recordMedianSlope_small ν hue e f hef htrans r hr) hT ht W hW y hy c hc hcmass
  exact tendstoInDistribution_pullback (fun i => sharedConditionedPairLaw ν ℓ 0 (y i)) μ
    (fun _ => Prod.fst) (fun _ => measurable_fst) (fun i => sharedConditionedPairLaw_fst ν ℓ (y i) hp)
    (fun i => recordLinearPath ℓ f (θ i) (r i) (n i) T)
    (fun i => measurable_recordLinearPath _ _ _ _ _ _) id W hlim

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
