import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyPrimeSquare
import OAI.NumberTheory.Ostmann.Construction.WordTransferFullPeriod

namespace OAI

/-! # Zero frequencies vanish in the original sampled histories -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem recursiveTransferWeight_nonzero_frequencies {State : Type*}
    (sys : TransferHistorySystem State) (leaf : State → ℤ → ℂ)
    (cutoff : State → ℤ → ℤ → ℤ → ℝ) (hleaf : ∀ x, leaf x 0 = 0)
    (n : ℕ) (x : State) (t : FrequencyTree ℤ n)
    (ht : recursiveTransferWeight sys leaf cutoff n x t ≠ 0) :
    ∀ s ∈ allFrequencyList n t, s ≠ 0 := by
  induction n generalizing x with
  | zero =>
    intro s hs
    have hst : s = t := by simpa only [allFrequencyList, List.mem_singleton] using hs
    subst s
    intro hz
    subst t
    exact ht (hleaf x)
  | succ n ih =>
    obtain ⟨P, hP, _, _⟩ := recursiveTransferWeight_nonzero_valid sys leaf cutoff _ x t ht
    rw [recursiveTransferWeight_node sys leaf cutoff n x t P hP] at ht
    have hL : recursiveTransferWeight sys leaf cutoff n (sys.leftState x P) t.2.1 ≠ 0 := by
      intro hz
      exact ht (by rw [hz, mul_zero, zero_mul])
    have hR : recursiveTransferWeight sys leaf cutoff n (sys.rightState x P) t.2.2 ≠ 0 := by
      intro hz
      exact ht (by rw [hz, star_zero, mul_zero])
    intro s hs
    simp only [allFrequencyList, List.mem_cons, List.mem_append] at hs
    rcases hs with rfl | hs | hs
    · exact hP.root_ne_zero
    · exact ih _ _ hL s hs
    · exact ih _ _ hR s hs

theorem movingSupportedSampledWeight_zero_frequency {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ) (hF : ∀ x, F x 0 = 0)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) (hz : ¬ ∀ s ∈ allFrequencyList n t, s ≠ 0) :
    movingSupportedSampledWeight value outside μ childBound pivotBound F E
      n t small bulk XL XR = 0 := by
  unfold movingSupportedSampledWeight movingSampledWeight
  apply Finset.sum_eq_zero
  intro a _
  suffices h : recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
      (movingGuardedLeaf value outside F)
      (movingSlotCutoff value childBound pivotBound
        (movingLocalExtra
          (movingGuardedExtra value outside (movingLocalExtra (movingCompensatedExtra value E)))))
      n ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t = 0 by
    rw [h, mul_zero]
  by_contra hn
  apply hz
  apply recursiveTransferWeight_nonzero_frequencies _ _ _ _ n _ t hn
  intro x
  simp only [movingGuardedLeaf, hF, ite_self]

theorem movingOriginalSampleAverage_zero_frequency {σ I : Type} [Fintype σ]
    (q : I → ℕ) [∀ i, Fact (q i).Prime] (value : σ → ℕ) (outside : List ℕ)
    (μ : ℕ → σ → ℝ) (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (hF : ∀ n (T : MovingSlotData σ n), F T 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (t : FrequencyTree ℤ n) (small bulk : TreeLeafTuple (List σ) n)
    (XL XR : ℕ) (hz : ¬ ∀ s ∈ allFrequencyList n t, s ≠ 0) :
    movingOriginalSampleAverage q value outside μ childBound pivotBound F g Dq S ψ X lo hi φ G
      n t small bulk XL XR = 0 := by
  rw [movingOriginalSampleAverage_eq]
  apply movingSupportedSampledWeight_zero_frequency value outside μ childBound pivotBound
    _ _ _ n t small bulk XL XR hz
  intro x
  simp only [movingOriginalLeaf, movingWindowLeaf, movingDataLeaf, hF, ite_self,
    zero_mul]

end Ostmann

end OAI
