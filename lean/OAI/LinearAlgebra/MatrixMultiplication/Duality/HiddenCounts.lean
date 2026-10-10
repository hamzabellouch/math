import OAI.LinearAlgebra.MatrixMultiplication.Completion.Partitions

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualHiddenRates

open MatrixMultiplication.Foundation RecursiveCompletion CompletionPartitions
attribute [local instance 10000] Classical.propDecidable Classical.decEq
attribute [local instance 11000] instDecidableEqFin

variable {X Y Z : Type*} [Fintype X]

theorem inactiveCount_minus_real (S : FlaggedTensor X Y Z) (m : ℕ) :
    (inactiveCount (complete S .B m) : ℝ) =
      ((activeCount S : ℝ) + (inactiveCount S : ℝ)) ^ m -
        (activeCount S : ℝ) ^ m := by
  have h := partition_count (complete S .B m)
  rw [activeCount_minus, Fintype.card_fun, Fintype.card_fin,
    ← partition_count S] at h
  have hreal : (activeCount S : ℝ) ^ m +
      (inactiveCount (complete S .B m) : ℝ) =
      ((activeCount S : ℝ) + (inactiveCount S : ℝ)) ^ m := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ℝ)) h
  linarith

theorem activeCount_plus_real (S : FlaggedTensor X Y Z) (center : Color)
    (hc : center ≠ .B) (m : ℕ) :
    (activeCount (complete S center m) : ℝ) =
      ((inactiveCount S : ℝ) + (activeCount S : ℝ)) ^ m -
        (inactiveCount S : ℝ) ^ m := by
  have h := partition_count (complete S center m)
  rw [inactiveCount_plus S center hc m, Fintype.card_fun,
    Fintype.card_fin, ← partition_count S] at h
  have hreal : (activeCount (complete S center m) : ℝ) +
      (inactiveCount S : ℝ) ^ m =
      ((activeCount S : ℝ) + (inactiveCount S : ℝ)) ^ m := by
    simpa only [Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ℝ)) h
  rw [add_comm (activeCount S : ℝ) (inactiveCount S : ℝ)] at hreal
  linarith

theorem activeFraction_ratio (S : FlaggedTensor X Y Z) :
    activeFraction S = (activeCount S : ℝ) /
      ((activeCount S : ℝ) + (inactiveCount S : ℝ)) := by
  rw [activeFraction, ← Nat.cast_add, partition_count]

theorem inactiveFraction_ratio [Nonempty X] (S : FlaggedTensor X Y Z) :
    1 - activeFraction S = (inactiveCount S : ℝ) /
      ((inactiveCount S : ℝ) + (activeCount S : ℝ)) := by
  rw [add_comm (inactiveCount S : ℝ) (activeCount S : ℝ),
    ← Nat.cast_add, partition_count]
  have h := fraction_sum S
  unfold inactiveFraction at h
  linarith

theorem counts_pos [Nonempty X] (S : FlaggedTensor X Y Z)
    (h0 : 0 < activeFraction S) (h1 : activeFraction S < 1) :
    0 < (activeCount S : ℝ) ∧ 0 < (inactiveCount S : ℝ) := by
  have hcard : (0 : ℝ) < Fintype.card X :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hi : 0 < inactiveFraction S := by
    linarith [fraction_sum S]
  constructor
  · exact (div_pos_iff_of_pos_right hcard).mp h0
  · exact (div_pos_iff_of_pos_right hcard).mp hi

end MatrixMultiplication.DualHiddenRates

end

end OAI
