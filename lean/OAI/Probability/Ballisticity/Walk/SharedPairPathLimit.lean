import Mathlib
import OAI.Probability.Ballisticity.Coupling.QuenchedMoments
import OAI.Probability.Ballisticity.Estimates.SharedLimitOccupation
import OAI.Probability.Ballisticity.Estimates.PairWeakUniqueness

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma probability_law_tendsto {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)] (X : ℕ → Ω → E)
    (hX : ∀ i, AEMeasurable (X i) (μ i)) (W : ProbabilityMeasure E)
    (h : TendstoInDistribution X atTop id μ W) :
    Tendsto (β := ProbabilityMeasure E) (fun i => (⟨(μ i).map (X i),
      (Measure.isProbabilityMeasure_map_iff (hX i)).mpr inferInstance⟩ : ProbabilityMeasure E))
      atTop (𝓝 W) := by
  have hh := h.tendsto
  have he : (⟨(W : Measure E).map id,
      (Measure.isProbabilityMeasure_map_iff h.aemeasurable_limit).mpr inferInstance⟩ : ProbabilityMeasure E)=W := by
    apply Subtype.ext
    exact Measure.map_id
  simpa only [he] using hh

theorem shared_pair_path_limit {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (T : ℝ) (hT : 0 < T) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      (∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
        (fun g : C(unitInterval,ℝ) => I.restrict g)=gaussianPathFiniteLaw (T/(2*commonMeanWidth ν ℓ)) I) ∧
      ∀ x : ℕ → Lattice d,
      ∀ μ : ℕ → ProbabilityMeasure RealPathPair,
      (∀ i, (μ i : Measure RealPathPair)=(sharedConditionedPairLaw ν ℓ (x i) (x i)).map
        (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
      Tendsto μ atTop (𝓝 (W.prod W)) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  obtain ⟨W,hW,hlim⟩ := shared_path_marginal_limits ν hue e f hef htrans r hr hT.le
  refine ⟨W,hW,?_⟩
  intro x μ hμ
  let η := fun i => sharedConditionedPairLaw ν ℓ (x i) (x i)
  have : ∀ i, IsProbabilityMeasure (η i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans _ _))
  let X := fun i (P : Path d × Path d) => recordLinearPath ℓ f (θ i) (r i) (n i) T (fun j => P.1 j-x i)
  let Y := fun i (P : Path d × Path d) => recordLinearPath ℓ f (θ i) (r i) (n i) T (fun j => P.2 j-x i)
  have hX (i : ℕ) : Measurable (X i) := (measurable_recordLinearPath _ _ _ _ _ _).comp (by fun_prop)
  have hY (i : ℕ) : Measurable (Y i) := (measurable_recordLinearPath _ _ _ _ _ _).comp (by fun_prop)
  obtain ⟨hf,hg⟩ := hlim x x (fun _ => rfl)
  have hMf : Tendsto (fun i => (μ i).map Prod.fst) atTop (𝓝 W) := by
    have hh := probability_law_tendsto η X (fun i => (hX i).aemeasurable) W hf
    apply hh.congr'
    filter_upwards [] with i
    symm
    apply Subtype.ext
    change (μ i : Measure RealPathPair).map Prod.fst=_
    rw [hμ i,Measure.map_map measurable_fst (measurable_sharedLinearPairPath _ _ _ _ _ _ _ _)]
    rfl
  have hMg : Tendsto (fun i => (μ i).map Prod.snd) atTop (𝓝 W) := by
    have hh := probability_law_tendsto η Y (fun i => (hY i).aemeasurable) W hg
    apply hh.congr'
    filter_upwards [] with i
    symm
    apply Subtype.ext
    change (μ i : Measure RealPathPair).map Prod.snd=_
    rw [hμ i,Measure.map_map measurable_snd (measurable_sharedLinearPairPath _ _ _ _ _ _ _ _)]
    rfl
  apply weak_limit_of_tight_identification μ (W.prod W) (pair_weak_tight μ W W hMf hMg)
  intro j hj V hV
  have hVf : (V : Measure RealPathPair).map Prod.fst=W := by
    have he := tendsto_nhds_unique
      ((ProbabilityMeasure.continuous_map continuous_fst).tendsto V |>.comp hV) (hMf.comp hj)
    exact congrArg (fun M : ProbabilityMeasure C(unitInterval,ℝ) => (M : Measure C(unitInterval,ℝ))) he
  have hVg : (V : Measure RealPathPair).map Prod.snd=W := by
    have he := tendsto_nhds_unique
      ((ProbabilityMeasure.continuous_map continuous_snd).tendsto V |>.comp hV) (hMg.comp hj)
    exact congrArg (fun M : ProbabilityMeasure C(unitInterval,ℝ) => (M : Measure C(unitInterval,ℝ))) he
  apply Subtype.ext
  exact shared_limit_product ν hue e f hef htrans (r ∘ j) (hr.comp hj) T hT (x ∘ j)
    (μ ∘ j) V hV W hW hVf hVg (fun i => hμ (j i))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma medianFirstHitPath_sub_linear {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d)
    (x : Lattice d) (θ r n T : ℝ) (X : Path d) :
    medianFirstHitPath ν ℓ hp f x r n T X-
      recordLinearPath ℓ f θ r n T (fun j => X j-x) =
      heightPolygon (fun h => (h:ℝ)*θ-(recordMedian ν ℓ hp f h:ℝ)) r n T := by
  exact heightPolygon_change_center _ _ _ _ _ _

lemma linear_add_median_error {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (f : Direction d)
    (x : Lattice d) (θ r n T : ℝ) (X : Path d) :
    recordLinearPath ℓ f θ r n T (fun j => X j-x)+
      heightPolygon (fun h => (h:ℝ)*θ-(recordMedian ν ℓ hp f h:ℝ)) r n T =
      medianFirstHitPath ν ℓ hp f x r n T X := by
  rw [← medianFirstHitPath_sub_linear ν ℓ hp f x θ r n T X]
  abel

lemma median_center_error_tendsto {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) {T : ℝ} (hT : 0 ≤ T) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    Tendsto (fun i => heightPolygon (fun h => (h:ℝ)*θ i-(recordMedian ν ℓ hp f h:ℝ))
      (r i) (n i) T) atTop (𝓝 0) := by
  dsimp only
  apply heightPolygon_tendsto_zero_of_grid _ _ _
    (recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1) T hT
  intro ε hε
  filter_upwards [recordMedian_linearization ν hue e f hef htrans r hr (T+1) hε] with i hi
  intro j hj
  simpa only [abs_div,abs_sub_comm] using hi j hj

theorem shared_median_pair_path_limit {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) (T : ℝ) (hT : 0 < T) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      (∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
        (fun g : C(unitInterval,ℝ) => I.restrict g)=gaussianPathFiniteLaw (T/(2*commonMeanWidth ν ℓ)) I) ∧
      ∀ x : ℕ → Lattice d,
      ∀ μ : ℕ → ProbabilityMeasure RealPathPair,
      (∀ i, (μ i : Measure RealPathPair)=(sharedConditionedPairLaw ν ℓ (x i) (x i)).map
        (fun P : Path d × Path d => (medianFirstHitPath ν ℓ hp f (x i) (r i) (n i) T P.1,
          medianFirstHitPath ν ℓ hp f (x i) (r i) (n i) T P.2))) →
      Tendsto μ atTop (𝓝 (W.prod W)) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  obtain ⟨W,hW,hlim⟩ := shared_pair_path_limit ν hue e f hef htrans r hr T hT
  refine ⟨W,hW,?_⟩
  intro x μ hμ
  let η := fun i => sharedConditionedPairLaw ν ℓ (x i) (x i)
  have : ∀ i, IsProbabilityMeasure (η i) := fun i => sharedConditionedPairLaw_probability ν ℓ _ _
    (ne_of_gt (sharedNoDropMass_pos ν hue ℓ (signed_direction_unit e) htrans _ _))
  let L := fun i => sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i)
  have hL (i : ℕ) : Measurable (L i) := measurable_sharedLinearPairPath _ _ _ _ _ _ _ _
  let V : ℕ → ProbabilityMeasure RealPathPair := fun i => ⟨(η i).map (L i),
    (Measure.isProbabilityMeasure_map_iff (hL i).aemeasurable).mpr inferInstance⟩
  have hV : Tendsto V atTop (𝓝 (W.prod W)) := hlim x V (fun i => rfl)
  let a := fun i => heightPolygon (fun h => (h:ℝ)*θ i-(recordMedian ν ℓ hp f h:ℝ)) (r i) (n i) T
  have ha : Tendsto a atTop (𝓝 0) := median_center_error_tendsto ν hue e f hef htrans r hr hT.le
  let addPair : RealPathPair × C(unitInterval,ℝ) → RealPathPair := fun z => (z.1.1+z.2,z.1.2+z.2)
  have hadd : Continuous addPair := by fun_prop
  have hh := weak_map_varying_parameter V (W.prod W) hV a 0 ha addPair hadd
  have he0 : (W.prod W).map (fun pair => addPair (pair,0))=W.prod W := by
    apply Subtype.ext
    change (↑(W.prod W) : Measure RealPathPair).map (fun P => addPair (P,0))=_
    simp only [addPair,add_zero,Prod.eta]
    exact Measure.map_id
  rw [he0] at hh
  apply hh.congr'
  filter_upwards [] with i
  apply Subtype.ext
  change ((η i).map (L i)).map (fun P => addPair (P,a i))=(μ i : Measure RealPathPair)
  rw [Measure.map_map (by fun_prop) (hL i),hμ i]
  congr 1
  funext P
  apply Prod.ext
  · exact linear_add_median_error ν ℓ hp f (x i) (θ i) (r i) (n i) T P.1
  · exact linear_add_median_error ν ℓ hp f (x i) (θ i) (r i) (n i) T P.2

end DirectionalTransience

end

end

end OAI
