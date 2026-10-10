import OAI.NumberTheory.Ostmann.Arithmetic.MovingSamplePrimeExpansion

namespace OAI

/-! # The original giant-prime mean as a sum of supported pattern means -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem movingOriginalSampleAverage_compensated {σ I : Type*} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi φ G
      n t small bulk XL XR =
    movingCompensatedAverage μ value n (fun a =>
      movingSupportedWeight value outside (buildMovingSlotData n t small bulk a) XL XR
        (movingOriginalGiantWeight q value childBound pivotBound F (fun _ _ _ _ => 1)
          g Dq S ψ X lo hi φ G (buildMovingSlotData n t small bulk a) t XL XR)) := by
  rw [movingOriginalSampleAverage_eq, movingSupportedSampledWeight_eq]
  congr 1
  funext a
  exact movingSupportedSampleTerm_original q value outside childBound pivotBound F g Dq S
    ψ X lo hi φ G n t small bulk XL XR a

/-- The finite original giant-prime square is exactly a sum of pattern means
of the original fully supported history pair. This is the input to the proved
prime-to-Page comparison; no prime is removed or reweighted here. -/
theorem movingOriginal_prime_pair_patterns {σ I : Type*} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : Bool → ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : Bool → FrequencyTree ℤ n) (small bulk : Bool → TreeLeafTuple (List σ) n)
    (u v r s : ℝ) :
    letI := sampleSetoidFintype (Bool × MovingSampleIndex n)
    let W := fun b x y => movingOriginalSampleAverage q value outside μ childBound pivotBound
      (F b) g (Dq b) S ψ X lo hi φ G n (t b) (small b) (bulk b) ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊
    let H := fun b x y a =>
      movingSupportedWeight value outside (buildMovingSlotData n (t b) (small b) (bulk b) a)
        ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊
        (movingOriginalGiantWeight q value childBound pivotBound (F b) (fun _ _ _ _ => 1)
          g (Dq b) S ψ X lo hi φ G (buildMovingSlotData n (t b) (small b) (bulk b) a) (t b)
          ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)
    complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
      W false x y * star (W true x y))) =
      ∑ eqp : Setoid (Bool × MovingSampleIndex n),
        ∑ z : {z : Quotient eqp → σ // Function.Injective z},
          let a := (movingSamplePairCoordinates σ n).symm (fun i => z.val (Quotient.mk'' i))
          (internalPatternWeight (fun i => Quotient.mk'' i)
            (fun i => μ (movingSampleTier i.2)) value z.val : ℂ) *
            complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
              H false x y a.1 * star (H true x y a.2))) := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  dsimp only
  simp_rw [movingOriginalSampleAverage_compensated]
  exact movingCompensatedAverage_prime_pair_patterns μ value n _ _ u v r s

end Ostmann

end OAI
