import OAI.NumberTheory.Ostmann.Construction.InitialMovingBulkTree
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotSystem
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSamplePrior

namespace OAI

/-! # Factoring terminal bulk weights from the original recursion -/

namespace Ostmann
open scoped Classical ComplexConjugate

/-- The logarithmic bulk cutoffs are independent of every reconstructed
pivot and survive the right-branch conjugations unchanged. -/
theorem movingSlotWeight_initial_halves {σ : Type*} (value : σ → ℕ) (b d r : ℕ) (cb cd : ℝ)
    (sl sr : Fin d → σ) (fallback : σ)
    (childBound pivotBound : ℕ → ℕ) (F : MovingSlotState σ → ℤ → ℂ)
    (cutoff : MovingSlotState σ → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) (t : FrequencyTree ℤ n) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => (initialMovingRealWeight value b d r cb cd sl sr
          (initialRegularFromList b r fallback x.data.regularSlots) : ℂ) * F x s)
        cutoff n ⟨n, T, XL, XR⟩ t =
      (initialMovingTreeWeight value b d r cb cd sl sr fallback T : ℂ) *
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
      simp only [initialMovingTreeWeight,
        Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    · exact (mul_zero _).symm

end Ostmann

end OAI
