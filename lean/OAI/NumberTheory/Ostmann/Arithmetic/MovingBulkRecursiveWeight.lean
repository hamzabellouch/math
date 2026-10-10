import OAI.NumberTheory.Ostmann.Arithmetic.MovingBulkLogWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotSystem
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSamplePrior

namespace OAI

/-! # Factoring terminal bulk weights from the original recursion -/

namespace Ostmann
open scoped Classical ComplexConjugate

/-- The logarithmic bulk cutoffs are independent of every reconstructed
pivot and survive the right-branch conjugations unchanged. -/
theorem movingSlotWeight_bulk_log {σ : Type*} (value : σ → ℕ) (tier : σ → ℕ)
    (k : ℕ) (outside : List ℕ) (cb cd : ℝ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (cutoff : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => (movingBulkLeafLogWeight value tier k outside cb cd x.data : ℂ) * F x s)
        cutoff n ⟨n, T, XL, XR⟩ t =
      (movingBulkTreeLogWeight value tier k outside cb cd T : ℂ) *
        recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
          F cutoff n ⟨n, T, XL, XR⟩ t := by
  induction T generalizing XL XR with
  | leaf => rfl
  | @node n s CL CR U left right ihL ihR =>
    simp only [recursiveTransferWeight]
    split_ifs
    · simp only [movingSlotSystem, MovingSlotState.child, ite_true,
        Bool.false_eq_true, ite_false] at ihL ihR ⊢
      rw [ihL, ihR]
      simp only [movingBulkTreeLogWeight,
        Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    · exact (mul_zero _).symm

/-- The unchanged independent law already enforces the tier of every
compensation prime, including repeated draws. -/
theorem movingCompensationPrior_levels {σ : Type*} (μ : σ → ℝ)
    (tier : σ → ℕ) (j : ℕ) (hμ : ∀ a, μ a ≠ 0 → tier a = j)
    (n : ℕ) (a : TreeLeafTuple (Fin 4 → σ) n)
    (ha : movingCompensationPrior μ n a ≠ 0) :
    ∀ i ∈ flattenMovingSlots n (movingCompensationSlots n a), tier i = j := by
  induction n with
  | zero =>
    intro i hi
    obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hi
    exact hμ _ (Finset.prod_ne_zero_iff.mp ha z (Finset.mem_univ z))
  | succ n ih =>
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact ih a.1 (left_ne_zero_of_mul ha) i hi
    · exact ih a.2 (right_ne_zero_of_mul ha) i hi

theorem movingSamplesPrior_levels {σ : Type*} (μ : ℕ → σ → ℝ)
    (tier : σ → ℕ) (hμ : ∀ j a, μ j a ≠ 0 → tier a = j)
    {n : ℕ} (a : MovingSampleSlots σ n) (ha : movingSamplesPrior μ a ≠ 0) :
    a.Levels tier := by
  induction a with
  | leaf => trivial
  | node u left right ihL ihR =>
    exact ⟨movingCompensationPrior_levels (μ _) tier _ (hμ _) _ u
      (left_ne_zero_of_mul (left_ne_zero_of_mul ha)),
      ihL (right_ne_zero_of_mul (left_ne_zero_of_mul ha)),
      ihR (right_ne_zero_of_mul ha)⟩

end Ostmann

end OAI
