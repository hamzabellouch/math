import OAI.NumberTheory.Ostmann.Arithmetic.MovingHistoryUniqueness
import OAI.NumberTheory.Ostmann.Preliminaries.TransferCauchy

namespace OAI

/-! # Frequency energy under the unchanged internal sample law -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingRootedFrequencyTree_injective (V : ℕ → ℕ) (n : ℕ) (s : ℤ) :
    Function.Injective (movingRootedFrequencyTree V n s) := by
  cases n with
  | zero =>
    change Function.Injective (fun _ : Unit => (s : ℤ))
    exact fun _ _ _ => Subsingleton.elim _ _
  | succ n =>
    intro a b h
    exact Prod.ext
      (scheduledFrequencyHistory_injective V n (congrArg (fun t => t.2.1) h))
      (scheduledFrequencyHistory_injective V n (congrArg (fun t => t.2.2) h))

private theorem norm_sum_sq_single_support {D : Type*} [Fintype D] (f : D → ℂ)
    (h : ∀ d e, f d ≠ 0 → f e ≠ 0 → d = e) :
    ‖∑ d, f d‖ ^ 2 = ∑ d, ‖f d‖ ^ 2 := by
  by_cases hf : ∃ d, f d ≠ 0
  · obtain ⟨d, hd⟩ := hf
    have hz (e) (he : e ≠ d) : f e = 0 := by
      by_contra hn
      exact he (h e d hn hd)
    rw [Fintype.sum_eq_single d hz, Fintype.sum_eq_single d]
    intro e he
    simp only [hz e he, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · push Not at hf
    simp only [hf, Finset.sum_const_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]

/-- Fixing the original samples makes the descendant sum have at most one
nonzero term. No bound by the number of frequency histories occurs. -/
theorem movingRecursiveWeight_root_energy {σ : Type*}
    (value : σ → ℕ) (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (s : ℤ) (small bulk : TreeLeafTuple (List σ) n)
    (a : MovingSampleSlots σ n) (XL XR : ℕ) :
    let W := fun t => recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound E) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t
    ‖∑ d : MovingDescendantFrequencyIndex V n, W (movingRootedFrequencyTree V n s d)‖ ^ 2 =
      ∑ d : MovingDescendantFrequencyIndex V n, ‖W (movingRootedFrequencyTree V n s d)‖ ^ 2 := by
  dsimp only
  apply norm_sum_sq_single_support
  intro d e hd he
  apply movingRootedFrequencyTree_injective V n s
  apply movingRecursiveWeight_history_unique value childBound pivotBound F E n _ _ small bulk a XL XR hd he
  cases n <;> rfl

theorem scheduledFrequency_sum_rooted_real (V : ℕ → ℕ) (n : ℕ)
    (f : FrequencyTree ℤ n → ℝ) :
    (∑ t : ScheduledFrequencyIndex V n, f (scheduledFrequencyHistory V n t)) =
      ∑ s : transferFrequencyRange (V n), ∑ t : MovingDescendantFrequencyIndex V n,
        f (movingRootedFrequencyTree V n s.val t) := by
  have he := (scheduledFrequencyRootEquiv V n).sum_comp
    (fun t => f (movingRootedFrequencyTree V n t.1.val t.2))
  simp_rw [← scheduledFrequencyRootEquiv_history] at he
  rw [Fintype.sum_prod_type] at he
  exact he

/-- Jensen is applied only to the original independent sample law, after
the unique-history square. All node compensations and guards remain in `W`. -/
theorem movingSampledWeight_frequency_energy {σ : Type*} [Fintype σ]
    (value : σ → ℕ) (μ : ℕ → σ → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a) (hmass : ∀ j, ∑ a, μ j a = 1)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (E : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    (n : ℕ) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    let W := fun t a => recursiveTransferWeight (movingSlotSystem value childBound pivotBound) F
      (movingSlotCutoff value childBound pivotBound (movingLocalExtra E)) n
      ⟨n, buildMovingSlotData n t small bulk a, XL, XR⟩ t
    (∑ s : transferFrequencyRange (V n),
      ‖∑ d : MovingDescendantFrequencyIndex V n,
        movingSampledWeight value μ childBound pivotBound F E n
          (movingRootedFrequencyTree V n s.val d) small bulk XL XR‖ ^ 2) ≤
      ∑ a : MovingSampleSlots σ n, movingSamplesPrior μ a *
        ∑ t : ScheduledFrequencyIndex V n, ‖W (scheduledFrequencyHistory V n t) a‖ ^ 2 := by
  intro W
  have hpoint (s : transferFrequencyRange (V n)) :
      ‖∑ d : MovingDescendantFrequencyIndex V n,
        movingSampledWeight value μ childBound pivotBound F E n
          (movingRootedFrequencyTree V n s.val d) small bulk XL XR‖ ^ 2 ≤
      ∑ a : MovingSampleSlots σ n, movingSamplesPrior μ a *
        ∑ d : MovingDescendantFrequencyIndex V n,
          ‖W (movingRootedFrequencyTree V n s.val d) a‖ ^ 2 := by
    simp only [movingSampledWeight]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    apply (probability_weighted_norm_sq_le (movingSamplesPrior μ)
      (movingSamplesPrior_nonneg μ hμ) (movingSamplesPrior_mass μ hmass n) _).trans_eq
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    exact movingRecursiveWeight_root_energy value childBound pivotBound V F
      (movingLocalExtra E) n s.val small bulk a XL XR
  calc
    _ ≤ ∑ s : transferFrequencyRange (V n), ∑ a : MovingSampleSlots σ n,
        movingSamplesPrior μ a * ∑ d : MovingDescendantFrequencyIndex V n,
          ‖W (movingRootedFrequencyTree V n s.val d) a‖ ^ 2 :=
      Finset.sum_le_sum (fun s _ => hpoint s)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum, ← scheduledFrequency_sum_rooted_real V n (fun t => ‖W t a‖ ^ 2)]

/-- The same estimate for the manuscript coefficient itself. The squared
node-product is explicit, ready for the arithmetic support estimate; the
spectators, Fourier factors and every support mask remain in the sample term. -/
theorem movingFrequencyCoefficient_energy {σ : Type} [Fintype σ]
    (value : σ → ℕ) (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (hμ : ∀ j a, 0 ≤ μ j a) (hmass : ∀ j, ∑ a, μ j a = 1)
    (childBound pivotBound V : ℕ → ℕ)
    (F : MovingSlotState σ → ℤ → ℂ) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (n : ℕ) (small bulk : TreeLeafTuple (List σ) n) (XL XR : ℕ) :
    (∑ s : transferFrequencyRange (V n),
      ‖movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
        n s.val small bulk XL XR‖ ^ 2) ≤
      ∑ a : MovingSampleSlots σ n, movingSamplesPrior μ a *
        (movingSampleProduct value a : ℝ) ^ 2 *
        ∑ t : ScheduledFrequencyIndex V n,
          ‖movingSupportedSampleTerm value outside childBound pivotBound F
            (movingOriginalNode value childBound pivotBound φ G) n
            (scheduledFrequencyHistory V n t) small bulk XL XR a‖ ^ 2 := by
  let E := movingOriginalNode value childBound pivotBound φ G
  have h := movingSampledWeight_frequency_energy value μ hμ hmass childBound pivotBound V
    (movingGuardedLeaf value outside F)
    (movingGuardedExtra value outside (movingLocalExtra (movingCompensatedExtra value E)))
    n small bulk XL XR
  change (∑ s : transferFrequencyRange (V n),
    ‖movingFrequencyCoefficient value outside μ childBound pivotBound V F φ G
      n s.val small bulk XL XR‖ ^ 2) ≤ _ at h
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  dsimp only
  rw [movingLocalExtra_guarded,
    movingSupportedWeight_recursive value outside childBound pivotBound F
      (movingLocalExtra (movingCompensatedExtra value E)) _ _
      (buildMovingSlotData_follows _ _ _ _ _),
    movingLocalExtra_compensated, movingRecursiveWeight_compensated, movingSupportedWeight_mul,
    norm_mul, mul_pow]
  simp only [Complex.norm_natCast]
  rfl

end Ostmann

end OAI
