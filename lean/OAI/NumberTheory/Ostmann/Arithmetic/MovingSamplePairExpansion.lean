import OAI.NumberTheory.Ostmann.Arithmetic.MovingRecursiveCompensation

namespace OAI

/-! # Exact paired expansion of the fully supported sampled coefficient

The equality-pattern scalar is the literal original prior times all node
compensations. The remaining coefficient retains every support test.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingCompensatedAverage {A : Type*} [Fintype A]
    (μ : ℕ → A → ℝ) (value : A → ℕ) (n : ℕ) (H : MovingSampleSlots A n → ℂ) : ℂ :=
  ∑ a, (((movingSampleProduct value a : ℝ) * movingSamplesPrior μ a : ℝ) : ℂ) * H a

theorem movingCompensatedAverage_pair {A : Type*} [Fintype A]
    (μ : ℕ → A → ℝ) (value : A → ℕ) (n : ℕ) (H K : MovingSampleSlots A n → ℂ) :
    movingCompensatedAverage μ value n H * star (movingCompensatedAverage μ value n K) =
      ∑ a, ∑ b, (movingPairCompensatedMass μ value (a, b) : ℂ) * H a * star (K b) := by
  unfold movingCompensatedAverage
  rw [star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [movingPairCompensatedMass, Complex.ofReal_mul, star_mul,
    Complex.star_def, Complex.conj_ofReal]
  ring

/-- The class assignments are injective, so coincidences are recorded exactly
once; no independence is ascribed to their induced law. -/
theorem movingCompensatedAverage_pair_patterns {A : Type*} [Fintype A]
    (μ : ℕ → A → ℝ) (value : A → ℕ) (n : ℕ) (H K : MovingSampleSlots A n → ℂ) :
    letI := sampleSetoidFintype (Bool × MovingSampleIndex n)
    movingCompensatedAverage μ value n H * star (movingCompensatedAverage μ value n K) =
      ∑ s : Setoid (Bool × MovingSampleIndex n),
        ∑ x : {x : Quotient s → A // Function.Injective x},
          let a := (movingSamplePairCoordinates A n).symm (fun i => x.val (Quotient.mk'' i))
          (internalPatternWeight (fun i => Quotient.mk'' i)
            (fun i => μ (movingSampleTier i.2)) value x.val : ℂ) * H a.1 * star (K a.2) := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  rw [movingCompensatedAverage_pair, sum_movingSamplePair_patterns]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  have h := movingPairCompensatedMass_pattern μ value n
    (fun i : Bool × MovingSampleIndex n => (Quotient.mk'' i : Quotient s)) x.val
  dsimp only [Function.comp_def] at h
  rw [h]

noncomputable def movingSupportedSampleTerm {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ) (childBound pivotBound : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) (a : MovingSampleSlots σ n) : ℂ :=
  movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
    (recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t)

noncomputable def movingSupportedSampledWeight {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) : ℂ :=
  movingSampledWeight value μ childBound pivotBound (movingGuardedLeaf value outside F)
    (movingGuardedExtra value outside (movingLocalExtra (movingCompensatedExtra value E)))
    n t small bulk XL XR

theorem movingSupportedSampledWeight_eq {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    movingSupportedSampledWeight value outside μ childBound pivotBound F E n t small bulk XL XR =
      movingCompensatedAverage μ value n
        (movingSupportedSampleTerm value outside childBound pivotBound F E n t small bulk XL XR) :=
  movingSampledWeight_compensated_supported value outside μ childBound pivotBound F E n t small bulk XL XR

/-- The original supported coefficient squared, in the coordinates used by
Section 8's arithmetic comparison. Neither support nor the original weights
are discarded in passing to equality patterns. -/
theorem movingSupportedSampledWeight_pair_patterns {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) :
    letI := sampleSetoidFintype (Bool × MovingSampleIndex n)
    let W := movingSupportedSampledWeight value outside μ childBound pivotBound F E n t small bulk XL XR
    let H := movingSupportedSampleTerm value outside childBound pivotBound F E n t small bulk XL XR
    W * star W = ∑ s : Setoid (Bool × MovingSampleIndex n),
      ∑ x : {x : Quotient s → σ // Function.Injective x},
        let a := (movingSamplePairCoordinates σ n).symm (fun i => x.val (Quotient.mk'' i))
        (internalPatternWeight (fun i => Quotient.mk'' i)
          (fun i => μ (movingSampleTier i.2)) value x.val : ℂ) * H a.1 * star (H a.2) := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  rw [movingSupportedSampledWeight_eq]
  exact movingCompensatedAverage_pair_patterns μ value n _ _

end Ostmann

end OAI
