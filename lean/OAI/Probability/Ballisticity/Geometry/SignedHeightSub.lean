import Mathlib
import OAI.Probability.Ballisticity.Estimates.SharedConditionedPairLawFst

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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma signedHeight_sub {d : ℕ} (e : Direction d) (x y : Lattice d) :
    signedHeight e (x-y) = signedHeight e x-signedHeight e y := by
  simp only [signedHeight,Pi.sub_apply]
  split <;> omega

theorem shared_path_marginal_limits {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let F := fun i => recordLinearPath ℓ f (recordMedianSlope ν ℓ hp f (r i)) (r i)
      (fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)) T
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      (∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
        (fun g : C(unitInterval,ℝ) => I.restrict g) =
          gaussianPathFiniteLaw (T/(2*commonMeanWidth ν ℓ)) I) ∧
      ∀ x y : ℕ → Lattice d, (∀ i, signedHeight e (x i) = signedHeight e (y i)) →
        letI : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ (x i) (y i)) := fun i =>
          sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
            (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
        TendstoInDistribution (fun i Z => F i (fun j => Z.1 j-x i))
          atTop id (fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)) W ∧
        TendstoInDistribution (fun i Z => F i (fun j => Z.2 j-y i))
          atTop id (fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)) W := by
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let F := fun i => recordLinearPath ℓ f (recordMedianSlope ν ℓ hp f (r i)) (r i)
    (fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)) T
  have hF (i : ℕ) : Measurable (F i) := measurable_recordLinearPath _ _ _ _ _ _
  obtain ⟨W,hW,hlim⟩ := shared_first_zero_path_limit ν hue e f hef htrans r hr hT
  have hfirst (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i)) :
      letI : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ (x i) (y i)) := fun i =>
        sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
          (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
      TendstoInDistribution (fun i Z => F i (fun j => Z.1 j-x i))
        atTop id (fun i => sharedConditionedPairLaw ν ℓ (x i) (y i)) W := by
    let : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ (x i) (y i)) := fun i =>
      sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
        (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
    let : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ 0 (y i-x i)) := fun i =>
      sharedConditionedPairLaw_probability ν ℓ 0 (y i-x i)
        (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans 0 (y i-x i)))
    have hy : ∀ i, signedHeight e (y i-x i) = 0 := fun i => by rw [signedHeight_sub,← hxy i,sub_self]
    have hm (i : ℕ) : (sharedConditionedPairLaw ν ℓ (x i) (y i)).map
        (fun Z : Path d × Path d => ((fun j => Z.1 j-x i),(fun j => Z.2 j-x i))) =
          sharedConditionedPairLaw ν ℓ 0 (y i-x i) := by
      simpa only [add_zero,add_sub_cancel] using sharedConditionedPairLaw_translation ν ℓ (x i) 0 (y i-x i)
    exact tendstoInDistribution_pullback _ _ _ (fun _ => by fun_prop) hm
      (fun i Z => F i Z.1) (fun i => (hF i).comp measurable_fst) id W (hlim _ hy)
  refine ⟨W,hW,fun x y hxy => ?_⟩
  let : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ (x i) (y i)) := fun i =>
    sharedConditionedPairLaw_probability ν ℓ (x i) (y i)
      (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (x i) (y i)))
  let : ∀ i, IsProbabilityMeasure (sharedConditionedPairLaw ν ℓ (y i) (x i)) := fun i =>
    sharedConditionedPairLaw_probability ν ℓ (y i) (x i)
      (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans (y i) (x i)))
  refine ⟨hfirst x y hxy,?_⟩
  exact tendstoInDistribution_pullback _ _ (fun _ => Prod.swap) (fun _ => measurable_swap)
    (fun i => sharedConditionedPairLaw_swap ν ℓ (x i) (y i))
    (fun i Z => F i (fun j => Z.1 j-y i)) (fun i => (hF i).comp (by fun_prop)) id W
    (hfirst y x (fun i => (hxy i).symm))

lemma joint_tight_of_marginal_limits {Ω Ω' E F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MetricSpace E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MetricSpace F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : ℕ → Ω → E) (Y : ℕ → Ω → F) (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (G : Ω' → E) (H : Ω' → F) (W : Measure Ω') [IsProbabilityMeasure W]
    (h₁ : TendstoInDistribution X atTop G μ W) (h₂ : TendstoInDistribution Y atTop H μ W) :
    IsTightMeasureSet (Set.range (fun i => (μ i).map (fun ω => (X i ω,Y i ω)))) := by
  have hx := distribution_sequence_tight μ X G W h₁
  have hy := distribution_sequence_tight μ Y H W h₂
  apply IsTightMeasureSet.prodMk
  · convert hx using 1
    ext η
    simp only [Set.mem_image,Set.mem_range,exists_exists_eq_and]
    simp only [Measure.fst,Measure.map_map measurable_fst ((hX _).prodMk (hY _)),Function.comp_def]
  · convert hy using 1
    ext η
    simp only [Set.mem_image,Set.mem_range,exists_exists_eq_and]
    simp only [Measure.snd,Measure.map_map measurable_snd ((hX _).prodMk (hY _)),Function.comp_def]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
