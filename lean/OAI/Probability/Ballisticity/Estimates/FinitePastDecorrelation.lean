import Mathlib
import OAI.Probability.Ballisticity.Estimates.WeakVaryingParameter
import OAI.Probability.Ballisticity.Estimates.WeightedTestPerturbation
import OAI.Probability.Ballisticity.Geometry.FinitePastCoordinates

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

theorem shared_finite_past_increment_decorrelation {d q : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (hn : ∀ i, 0 < fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i))
    (T : ℝ) (hT : 0 < T) (k : ℕ → ℕ)
    (hk : ∀ i, (k i:ℝ) ≤ T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i))
    (t : ℝ) (hkt : Tendsto (fun i => (k i:ℝ)/fluctuationScale
      (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i)) atTop (𝓝 t))
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i))
    (H : ℕ → ℕ) (hH : ∀ i, 0 < H i) (j : ℕ → Fin q → ℕ) (hj : ∀ i a, j i a ≤ H i)
    (F : ℕ → (Fin q → ℝ × ℝ) → ℝ) (C : ℝ) (hC : 0 ≤ C) (hF : ∀ i z, ‖F i z‖ ≤ C)
    (G : ℝ →ᵇ ℝ) (hG : UniformContinuous G) (b : Bool) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    Tendsto (fun i => ∫ P, F i (centeredPastCoordinates ℓ f (θ i) (r i) (j i) (x i) (y i) P) *
      (G (centeredHitIncrement ℓ f (θ i) (r i) (H i) (k i)
        (pairSide b (x i,y i)) (pairSide b P))-
        (∫ z, G z ∂gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ)))))
      ∂sharedConditionedPairLaw ν ℓ (x i) (y i)) atTop (𝓝 0) := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  let F' := fun i D => F i (centeredPastCoordinates ℓ f (θ i) (r i) (j i) (x i) (y i)
    (boundaryPrefixPair D))
  have hh := shared_deterministic_increment_decorrelation ν hue e f hef htrans r hr hn T hT
    k hk t hkt x y hxy H hH F' C hC (fun i D => hF i _) G hG b
  apply hh.congr'
  filter_upwards [] with i
  apply integral_congr_ae
  filter_upwards [shared_centeredPastCoordinates_boundary ν hue e f htrans (x i) (y i)
    (hxy i) (H i) (hH i) (j i) (hj i) (θ i) (r i)] with P hP
  dsimp only [F']
  rw [hP]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

abbrev RealPathPair := C(unitInterval,ℝ) × C(unitInterval,ℝ)
abbrev JointPastTimes (q : ℕ) := (Fin q → unitInterval) × unitInterval × unitInterval

noncomputable def jointPastIncrementMap {q : ℕ} (b : Bool) :
    C(RealPathPair × JointPastTimes q, (Fin q → ℝ × ℝ) × ℝ) where
  toFun z := ((fun a => (z.1.1 (z.2.1 a), z.1.2 (z.2.1 a))),
    if b then z.1.2 z.2.2.2 - z.1.2 z.2.2.1 else z.1.1 z.2.2.2 - z.1.1 z.2.2.1)
  continuous_toFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro a
      exact (continuous_eval.comp (continuous_fst.fst.prodMk (continuous_apply a |>.comp continuous_snd.fst))).prodMk
        (continuous_eval.comp (continuous_fst.snd.prodMk (continuous_apply a |>.comp continuous_snd.fst)))
    · cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · exact (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd.snd.snd)).sub
          (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd.snd.fst))
      · exact (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd.snd.snd)).sub
          (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd.snd.fst))

noncomputable def jointPastProductTest {q : ℕ} (F : (Fin q → ℝ × ℝ) →ᵇ ℝ)
    (G : ℝ →ᵇ ℝ) (c : ℝ) : ((Fin q → ℝ × ℝ) × ℝ) →ᵇ ℝ :=
  (F.compContinuous ⟨Prod.fst,continuous_fst⟩) *
    ((G.compContinuous ⟨Prod.snd,continuous_snd⟩)-BoundedContinuousFunction.const _ c)

lemma weak_joint_past_integral {q : ℕ} (μ : ℕ → ProbabilityMeasure RealPathPair)
    (V : ProbabilityMeasure RealPathPair) (hμ : Tendsto μ atTop (𝓝 V))
    (a : ℕ → JointPastTimes q) (a₀ : JointPastTimes q) (ha : Tendsto a atTop (𝓝 a₀))
    (b : Bool) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (G : ℝ →ᵇ ℝ) (c : ℝ) :
    Tendsto (fun i => ∫ P, jointPastProductTest F G c (jointPastIncrementMap b (P,a i)) ∂(μ i : Measure RealPathPair))
      atTop (𝓝 (∫ P, jointPastProductTest F G c (jointPastIncrementMap b (P,a₀)) ∂(V : Measure RealPathPair))) := by
  have hm := weak_map_varying_parameter μ V hμ a a₀ ha (jointPastIncrementMap b)
    (jointPastIncrementMap b).continuous
  have hh := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hm) (jointPastProductTest F G c)
  have he (U : ProbabilityMeasure RealPathPair) (u : JointPastTimes q) :
      (∫ z, jointPastProductTest F G c z ∂(U.map
        (fun paths => jointPastIncrementMap b (paths,u)) : Measure _)) =
      ∫ P, jointPastProductTest F G c (jointPastIncrementMap b (P,u)) ∂(U : Measure RealPathPair) := by
    change (∫ z, jointPastProductTest F G c z ∂(U : Measure RealPathPair).map
      (fun P => jointPastIncrementMap b (P,u))) = _
    exact integral_map
      (((jointPastIncrementMap b).continuous.comp (continuous_id.prodMk continuous_const)).measurable.aemeasurable)
      (jointPastProductTest F G c).continuous.aestronglyMeasurable
  simpa only [he] using hh

lemma joint_past_identity_of_prelimit {q : ℕ} (μ : ℕ → ProbabilityMeasure RealPathPair)
    (V : ProbabilityMeasure RealPathPair) (hμ : Tendsto μ atTop (𝓝 V))
    (a : ℕ → JointPastTimes q) (a₀ : JointPastTimes q) (ha : Tendsto a atTop (𝓝 a₀))
    (b : Bool) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (G : ℝ →ᵇ ℝ) (c : ℝ)
    (hd : Tendsto (fun i => ∫ P, jointPastProductTest F G c (jointPastIncrementMap b (P,a i))
      ∂(μ i : Measure RealPathPair)) atTop (𝓝 0)) :
    (∫ P, jointPastProductTest F G c (jointPastIncrementMap b (P,a₀)) ∂(V : Measure RealPathPair)) = 0 :=
  tendsto_nhds_unique (weak_joint_past_integral μ V hμ a a₀ ha b F G c) hd

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def sharedLinearPairPath {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (x y : Lattice d) (P : Path d × Path d) : RealPathPair :=
  (recordLinearPath ℓ f θ r n T (fun j => P.1 j-x),
    recordLinearPath ℓ f θ r n T (fun j => P.2 j-y))

lemma measurable_sharedLinearPairPath {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (x y : Lattice d) : Measurable (sharedLinearPairPath ℓ f θ r n T x y) := by
  exact ((measurable_recordLinearPath ℓ f θ r n T).comp (by fun_prop)).prodMk
    ((measurable_recordLinearPath ℓ f θ r n T).comp (by fun_prop))

lemma recordLinearPath_grid {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (h : 0 ≤ T*n) (x : Lattice d) (X : Path d)
    (j : ℕ) (t : unitInterval) (ht : T*n*(t:ℝ) = j) :
    recordLinearPath ℓ f θ r n T (fun k => X k-x) t = centeredFirstHit ℓ f θ r j x X :=
  heightPolygon_grid _ r n T h j t ht

lemma jointPastIncrementMap_grid {d q : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (h : 0 ≤ T*n) (x y : Lattice d) (P : Path d × Path d)
    (j : Fin q → ℕ) (H k : ℕ) (a : JointPastTimes q)
    (hj : ∀ z, T*n*(a.1 z:ℝ) = j z) (hH : T*n*(a.2.1:ℝ) = H)
    (hk : T*n*(a.2.2:ℝ) = H+k) (b : Bool) :
    jointPastIncrementMap b (sharedLinearPairPath ℓ f θ r n T x y P,a) =
      (centeredPastCoordinates ℓ f θ r j x y P,
        centeredHitIncrement ℓ f θ r H k (pairSide b (x,y)) (pairSide b P)) := by
  apply Prod.ext
  · funext z
    apply Prod.ext
    · exact recordLinearPath_grid ℓ f θ r n T h x P.1 (j z) (a.1 z) (hj z)
    · exact recordLinearPath_grid ℓ f θ r n T h y P.2 (j z) (a.1 z) (hj z)
  · cases b <;> simp only [jointPastIncrementMap,ContinuousMap.coe_mk,sharedLinearPairPath,
      Bool.false_eq_true,ite_false,ite_true,pairSide]
    · rw [recordLinearPath_grid ℓ f θ r n T h x P.1 (H+k) a.2.2 (by simpa using hk),
        recordLinearPath_grid ℓ f θ r n T h x P.1 H a.2.1 hH]
      simp only [centeredFirstHit,centeredHitIncrement,Nat.cast_add]
      ring
    · rw [recordLinearPath_grid ℓ f θ r n T h y P.2 (H+k) a.2.2 (by simpa using hk),
        recordLinearPath_grid ℓ f θ r n T h y P.2 H a.2.1 hH]
      simp only [centeredFirstHit,centeredHitIncrement,Nat.cast_add]
      ring

end DirectionalTransience

end

end

end OAI
