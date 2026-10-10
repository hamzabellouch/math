import Mathlib
import OAI.Probability.Ballisticity.Estimates.FinitePastDecorrelation

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

theorem shared_limit_finite_past_identity {d q : ℕ} (ν : Measure (Row d))
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
    (H : ℕ → ℕ) (hH : ∀ i, 0 < H i) (j : ℕ → Fin q → ℕ) (hj : ∀ i z, j i z ≤ H i)
    (a : ℕ → JointPastTimes q) (a₀ : JointPastTimes q) (ha : Tendsto a atTop (𝓝 a₀))
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V))
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (G : ℝ →ᵇ ℝ) (hG : UniformContinuous G) (b : Bool) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i z, T*n i*(a i |>.1 z : ℝ) = j i z) →
    (∀ i, T*n i*(a i |>.2.1 : ℝ) = H i) →
    (∀ i, T*n i*(a i |>.2.2 : ℝ) = H i+k i) →
    (∀ i, (μ i : Measure RealPathPair) = (sharedConditionedPairLaw ν ℓ (x i) (y i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (y i))) →
    (∫ P, jointPastProductTest F G (∫ z, G z ∂gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ))))
      (jointPastIncrementMap b (P,a₀)) ∂(V : Measure RealPathPair)) = 0 := by
  dsimp only
  intro haj haH hak hμ
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  let c := ∫ z, G z ∂gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ)))
  have hd := shared_finite_past_increment_decorrelation ν hue e f hef htrans r hr hn T hT k hk t hkt
    x y hxy H hH j hj (fun _ => F) ‖F‖ (norm_nonneg _) (fun _ z => F.norm_coe_le_norm z) G hG b
  apply joint_past_identity_of_prelimit μ V hweak a a₀ ha b F G c
  apply hd.congr'
  filter_upwards [] with i
  rw [hμ i]
  have htest : Continuous (fun P : RealPathPair => jointPastProductTest F G c (jointPastIncrementMap b (P,a i))) :=
    (jointPastProductTest F G c).continuous.comp ((jointPastIncrementMap b).continuous.comp
      (continuous_id.prodMk continuous_const))
  rw [integral_map (measurable_sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (y i)).aemeasurable
    htest.aestronglyMeasurable]
  apply integral_congr_ae
  apply ae_of_all
  intro P
  dsimp only
  rw [jointPastIncrementMap_grid ℓ f (θ i) (r i) (n i) T (mul_nonneg hT.le (hn i).le)
    (x i) (y i) P (j i) (H i) (k i) (a i) (haj i) (haH i) (hak i) b]
  rfl

end DirectionalTransience

end

end

end OAI
