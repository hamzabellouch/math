import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeCoefficientNode
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRegularSlots

namespace OAI

/-! # Current support inherited from the original summed coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingFullSupport_local {σ : Type*} (value : σ → ℕ) (outside : List ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ)
    (h : movingFullSupport value outside T XL XR) :
    movingLocalSupport value outside ⟨n, T, XL, XR⟩ := by
  cases T with
  | leaf => exact h
  | node => exact ⟨h.1.1, h.2.1⟩

/-- A nonzero finite average contains a supported original sample. No
positivity, normalization, or conditioning of the prime prior is needed. -/
theorem movingSupportedSampledWeight_nonzero_support {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ)
    (h : movingSupportedSampledWeight value outside μ childBound pivotBound F E
      n t small bulk XL XR ≠ 0) :
    ∃ a : MovingSampleSlots σ n,
      movingFullSupport value outside (buildMovingSlotData n t small bulk a) XL XR := by
  rw [movingSupportedSampledWeight_eq, movingCompensatedAverage] at h
  obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have ht : movingSupportedSampleTerm value outside childBound pivotBound F E
      n t small bulk XL XR a ≠ 0 := by
    intro hz
    exact ha (by rw [hz, mul_zero])
  unfold movingSupportedSampleTerm movingSupportedWeight at ht
  refine ⟨a, ?_⟩
  by_contra hs
  exact ht (ite_eq_right hs)

/-- The root sum still has the actual current pairwise support and both
root-frequency units. These are the only support facts needed to attach the
original coefficient to the full Fourier transfer. -/
theorem movingFrequencyCoefficient_nonzero_support {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n : ℕ) (s : ℤ)
    (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ)
    (h : movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      n s small bulk XL XR ≠ 0) :
    (XL :: XR :: ((flattenMovingSlots n small ++ flattenMovingSlots n bulk).map value ++ outside)).Pairwise Nat.Coprime ∧
      IsCoprime (XL : ℤ) s ∧ IsCoprime (XR : ℤ) s := by
  rw [movingFrequencyCoefficient] at h
  obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨a, ha⟩ := movingSupportedSampledWeight_nonzero_support value outside μ childBound
    pivotBound F (movingOriginalNode value childBound pivotBound φ G) n
    (movingRootedFrequencyTree V n s t) small bulk XL XR ht
  let T := buildMovingSlotData n (movingRootedFrequencyTree V n s t) small bulk a
  have hlocal := movingFullSupport_local value outside T XL XR ha
  have hreg := buildMovingSlotData_regular_perm n (movingRootedFrequencyTree V n s t) small bulk a
  have hp : (T.currentSlots value XL XR ++ outside).Perm
      (XL :: XR :: ((flattenMovingSlots n small ++ flattenMovingSlots n bulk).map value ++ outside)) := by
    simpa only [MovingSlotData.currentSlots, List.cons_append] using
      (((hreg.map value).cons XR).cons XL).append_right outside
  have hpair := (hp.pairwise_iff (fun h => h.symm)).mp hlocal.1
  have hfreq : T.frequency = s := by
    rw [(buildMovingSlotData_follows n _ small bulk a).root, movingRootedFrequencyTree_root]
  have hL := ((T.frequencies_isCoprime (XL : ℤ)).mpr hlocal.2.1).root
  have hR := ((T.frequencies_isCoprime (XR : ℤ)).mpr hlocal.2.2.1).root
  exact ⟨hpair, hfreq ▸ hL, hfreq ▸ hR⟩

end Ostmann

end OAI
