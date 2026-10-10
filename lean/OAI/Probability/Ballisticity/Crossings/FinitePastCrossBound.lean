import Mathlib
import OAI.Probability.Ballisticity.Crossings.ContinuousCrossPast
import OAI.Probability.Ballisticity.Crossings.DeterministicCrossBound

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma shared_finite_past_cross_bound {d q : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0<r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i)=signedHeight e (y i))
    (H : ℕ → ℕ) (hH : ∀ i, 0<H i) (j : ℕ → Fin q → ℕ) (hj : ∀ i z, j i z≤H i)
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ)
    (g : ℝ →ᵇ ℝ) (hg : UniformContinuous g) (hgb : ∀ z, |g z|≤1)
    {a t : ℝ} (ha : 0<a) (ht : 0<t) (hgzero : ∀ z, |z|≤a → g z=0)
    (w : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    ∀ᶠ i in atTop, |∫ P, F (centeredPastCoordinates ℓ f (θ i) (r i) (j i) (x i) (y i) P)*
      (g (physicalFirstHitGap ℓ f (x i) (y i) (H i) P/r i)*
      (symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) ⌊t*n i⌋₊ (x i) P.1)*
      symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) ⌊t*n i⌋₊ (y i) P.2)))
      ∂sharedConditionedPairLaw ν ℓ (x i) (y i)| ≤
      ‖F‖*(16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t)))+ε := by
  dsimp only
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  let F' := fun i D => F (centeredPastCoordinates ℓ f (θ i) (r i) (j i) (x i) (y i) (boundaryPrefixPair D))
  have hh := shared_deterministic_cross_bound ν hue e f hef htrans r hrpos hr x y hxy H hH F'
    ‖F‖ (norm_nonneg _) (fun i D => F.norm_coe_le_norm _) g hg hgb ha ht hgzero w hε
  filter_upwards [hh] with i hi
  convert hi using 2
  apply integral_congr_ae
  filter_upwards [shared_centeredPastCoordinates_boundary ν hue e f htrans (x i) (y i) (hxy i)
    (H i) (hH i) (j i) (hj i) (θ i) (r i)] with P hP
  dsimp only [F']
  rw [hP]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

theorem shared_limit_finite_past_cross_bound {d q : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hrpos : ∀ i, 0<r i)
    (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (hn : ∀ i, 0 < fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i))
    (T : ℝ) (hT : 0<T) (x : ℕ → Lattice d)
    (H : ℕ → ℕ) (hH : ∀ i, 0<H i) (j : ℕ → Fin q → ℕ) (hj : ∀ i z, j i z≤H i)
    (u : ℕ → JointPastTimes q) (u₀ : JointPastTimes q) (hu : Tendsto u atTop (𝓝 u₀))
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V)) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ)
    (g : ℝ →ᵇ ℝ) (hg : UniformContinuous g) (hgb : ∀ z, |g z|≤1)
    {a t : ℝ} (ha : 0<a) (ht : 0<t) (hgzero : ∀ z, |z|≤a → g z=0) (w : ℝ≥0) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i z, T*n i*(u i |>.1 z : ℝ)=j i z) →
    (∀ i, T*n i*(u i |>.2.1 : ℝ)=H i) →
    (∀ i, T*n i*(u i |>.2.2 : ℝ)=H i+⌊t*n i⌋₊) →
    (∀ i, (μ i : Measure RealPathPair)=(sharedConditionedPairLaw ν ℓ (x i) (x i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
    |∫ P, jointCrossPastTest F (symmetricClip w) g (P,u₀) ∂(V : Measure RealPathPair)| ≤
      ‖F‖*(16*‖symmetricClip w‖^2*Real.exp (-commonMeanWidth ν ℓ*a^2/(9*t))) := by
  dsimp only
  intro huj huH huk hμ
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
  let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
  have hc := (weak_joint_cross_past_integral μ V hweak u u₀ hu F (symmetricClip w) g).abs
  apply le_of_forall_pos_le_add
  intro ε hε
  apply le_of_tendsto hc
  have hh := shared_finite_past_cross_bound ν hue e f hef htrans r hrpos hr x x (fun _ => rfl)
    H hH j hj F g hg hgb ha ht hgzero w hε
  filter_upwards [hh] with i hi
  have he : (∫ P, jointCrossPastTest F (symmetricClip w) g (P,u i) ∂(μ i : Measure RealPathPair)) =
      ∫ P, F (centeredPastCoordinates ℓ f (θ i) (r i) (j i) (x i) (x i) P)*
        (g (physicalFirstHitGap ℓ f (x i) (x i) (H i) P/r i)*
        (symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) ⌊t*n i⌋₊ (x i) P.1)*
         symmetricClip w (centeredHitIncrement ℓ f (θ i) (r i) (H i) ⌊t*n i⌋₊ (x i) P.2)))
        ∂sharedConditionedPairLaw ν ℓ (x i) (x i) := by
    rw [hμ i]
    have htest : Continuous (fun P : RealPathPair => jointCrossPastTest F (symmetricClip w) g (P,u i)) :=
      (jointCrossPastTest F (symmetricClip w) g).continuous.comp (continuous_id.prodMk continuous_const)
    rw [integral_map (measurable_sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i)).aemeasurable
      htest.aestronglyMeasurable]
    apply integral_congr_ae
    apply ae_of_all
    intro P
    exact jointCrossPastTest_grid ℓ f (θ i) (r i) (n i) T (mul_nonneg hT.le (hn i).le)
      (x i) P (j i) (H i) ⌊t*n i⌋₊ (u i) (huj i) (huH i) (huk i) F (symmetricClip w) g
  rw [he]
  exact hi

end DirectionalTransience

end

end

end OAI
