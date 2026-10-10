import Mathlib
import OAI.Probability.Ballisticity.Walk.JointPathIndependence
import OAI.Probability.Ballisticity.Crossings.SharedInteriorCross
import OAI.Probability.Ballisticity.Estimates.SharedLimitNormalPast
import OAI.Probability.Ballisticity.Estimates.OccupationLimit

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma shared_gap_at_grid {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (h : 0 < T*n) (x : Lattice d) (P : Path d × Path d)
    (j : ℕ) (hj : (j:ℝ) ≤ T*n) :
    layerGap (sharedLinearPairPath ℓ f θ r n T x x P) (layerGridPoint (T*n) j) =
      -(physicalFirstHitGap ℓ f x x j P)/r := by
  have ht : T*n*(layerGridPoint (T*n) j : ℝ) = j := by
    rw [layerGridPoint_coe h hj]
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ h.ne'
  dsimp only [layerGap,sharedLinearPairPath]
  rw [recordLinearPath_grid ℓ f θ r n T h.le x P.1 j _ ht,
    recordLinearPath_grid ℓ f θ r n T h.le x P.2 j _ ht]
  have hz : signedCoordinate f (0 : Lattice d) = 0 := by simp [signedCoordinate]
  simp only [centeredFirstHit,physicalFirstHitGap,firstHitPairGap,sub_self,hz,zero_add]
  simp only [sub_eq_add_neg,add_comm]
  ring

lemma shared_gridOccupation_eq {d : ℕ} (ν : Measure (Row d)) (e f : Direction d)
    (θ r n T ρ : ℝ) (hr : 0 < r) (h : 0 < T*n) (x : Lattice d) :
    gridOccupationMass ((sharedConditionedPairLaw ν (realPosition (step e)) x x).map
      (sharedLinearPairPath (realPosition (step e)) f θ r n T x x)) (T*n) ρ =
      firstHitOccupationMean ν e f x x (ρ*r) (⌊T*n⌋₊+1)/(T*n) := by
  unfold gridOccupationMass firstHitOccupationMean
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : (j:ℝ) ≤ T*n := (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).trans (Nat.floor_le h.le)
  have hs : MeasurableSet {P : RealPathPair | |layerGap P (layerGridPoint (T*n) j)| ≤ ρ} :=
    (isClosed_le (show Continuous (fun P : RealPathPair => |layerGap P (layerGridPoint (T*n) j)|) from
      (continuous_layerGap.comp (continuous_id.prodMk continuous_const)).abs) continuous_const).measurableSet
  rw [Measure.real,Measure.map_apply (measurable_sharedLinearPairPath _ _ _ _ _ _ _ _) hs]
  congr 2
  ext P
  change |layerGap (sharedLinearPairPath _ _ _ _ _ _ _ _ P) (layerGridPoint (T*n) j)| ≤ ρ ↔ _
  rw [shared_gap_at_grid _ _ _ _ _ _ h _ _ j hjn,abs_div,abs_neg,abs_of_pos hr]
  exact div_le_iff₀ hr

theorem shared_limit_diagonal_time_zero {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x : ℕ → Lattice d) {T : ℝ} (hT : 0 < T)
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V)) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i, (μ i : Measure RealPathPair) = (sharedConditionedPairLaw ν ℓ (x i) (x i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
    ((V : Measure RealPathPair).prod volume) {z : RealPathPair × unitInterval | layerGap z.1 z.2 = 0} = 0 := by
  dsimp only
  intro hμ
  let ℓ := realPosition (step e)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  have hn : Tendsto n atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans r hr.1
  apply joint_limit_diagonal_time_zero μ V hweak (weak_sequence_tight hweak) (fun i => T*n i) (hn.const_mul_atTop hT)
  intro ε hε
  obtain ⟨ρ,hρ,ho⟩ := shared_first_hit_occupation_vanishes ν hue e f hef htrans r hr x hT (mul_pos hε hT)
  refine ⟨ρ,hρ,?_⟩
  filter_upwards [ho,hr.1.eventually_gt_atTop 0,hn.eventually_gt_atTop 0] with i hi hri hni
  rw [hμ i,shared_gridOccupation_eq ν e f _ _ _ _ ρ hri (mul_pos hT hni)]
  calc
    _ = (firstHitOccupationMean ν e f (x i) (x i) (ρ*r i) (⌊T*n i⌋₊+1)/n i)/T := by
      rw [div_div,mul_comm T]
    _ ≤ ε := (div_le_iff₀ hT).mpr hi

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma shared_limit_product {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (T : ℝ) (hT : 0 < T) (x : ℕ → Lattice d)
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V))
    (W : ProbabilityMeasure C(unitInterval,ℝ))
    (hW : ∀ I : Finset unitInterval, (W : Measure C(unitInterval,ℝ)).map
      (fun g : C(unitInterval,ℝ) => I.restrict g)=
        gaussianPathFiniteLaw (T/(2*commonMeanWidth ν (realPosition (step e)))) I)
    (hf : (V : Measure RealPathPair).map Prod.fst=W)
    (hg : (V : Measure RealPathPair).map Prod.snd=W) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i, (μ i : Measure RealPathPair)=(sharedConditionedPairLaw ν ℓ (x i) (x i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
    (V : Measure RealPathPair)=(W : Measure C(unitInterval,ℝ)).prod W := by
  dsimp only
  intro hμ
  let ℓ := realPosition (step e)
  let c := Real.toNNReal (T/(2*commonMeanWidth ν ℓ))
  have hc := commonMeanWidth_ge_one ν ℓ htrans (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)
  have h := shared_limit_normalJointPast ν hue e f hef htrans r hr T hT x μ V hweak hμ
  have hz := shared_limit_diagonal_time_zero ν hue e f hef htrans r hr x hT μ V hweak hμ
  have hcross : SeparatedCrossBound (V : Measure RealPathPair)
      (commonMeanWidth ν ℓ/(9*T)) (16*‖symmetricClip 1‖^2) := by
    intro q v s t hv hst ht F g hg hgb ρ hρ hgzero
    have hh := shared_limit_interior_cross_bound ν hue e f hef htrans r hr T hT x μ V hweak
      v s t hv hst ht F g hg hgb hρ hgzero 1 hμ
    have hexp : -(commonMeanWidth ν ℓ/(9*T))*ρ^2/((t:ℝ)-s) =
        -commonMeanWidth ν ℓ*ρ^2/(9*(T*((t:ℝ)-s))) := by
      field_simp
    rw [hexp]
    simpa only [jointCrossPastTest_apply,pairPastCoordinates,pairPathIncrement,
      ContinuousMap.coe_mk,Bool.false_eq_true,ite_false,ite_true,mul_assoc] using hh
  have hW0 := wiener_path_initial_zero W _ hW
  have h0f : ∀ᵐ P ∂(V : Measure RealPathPair),P.1 0=0 := by
    have hh : ∀ᵐ P ∂(V : Measure RealPathPair).map Prod.fst,P 0=0 := by rw [hf]; exact hW0
    exact (ae_map_iff measurable_fst.aemeasurable ((isClosed_eq (continuous_eval_const 0) continuous_const).measurableSet)).mp hh
  have h0g : ∀ᵐ P ∂(V : Measure RealPathPair),P.2 0=0 := by
    have hh : ∀ᵐ P ∂(V : Measure RealPathPair).map Prod.snd,P 0=0 := by rw [hg]; exact hW0
    exact (ae_map_iff measurable_snd.aemeasurable ((isClosed_eq (continuous_eval_const 0) continuous_const).measurableSet)).mp hh
  have he := normalJointPast_product_identification (V : Measure RealPathPair) c h
    (by positivity : 0 < commonMeanWidth ν ℓ/(9*T)) (by positivity : 0 ≤ 16*‖symmetricClip 1‖^2)
    hcross (by
      have hs : {z : RealPathPair × unitInterval | z.1.1 z.2-z.1.2 z.2=0} =
          {z : RealPathPair × unitInterval | layerGap z.1 z.2=0} := by
        ext z
        change z.1.1 z.2-z.1.2 z.2=0 ↔ z.1.2 z.2-z.1.1 z.2=0
        rw [sub_eq_zero,sub_eq_zero,eq_comm]
      rw [hs]
      exact hz) (h0f.and h0g)
  simpa only [hf,hg] using he

end DirectionalTransience

end

end

end OAI
