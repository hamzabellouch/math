import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition

namespace OAI

section

namespace Erdos3

open Polynomial
open scoped NNReal

theorem PolynomialIntervalPowerBound.polynomial_block_reduction
    {j C e : ℕ} (hW : PolynomialIntervalPowerBound (j + 1) C e)
    {ι : Type*} [Fintype ι] (P : ι → Polynomial ℝ)
    (hP : ∀ i, (P i).natDegree ≤ j + 1) (N H : ℕ) (hH : 0 < H)
    (hscale : schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) ≤ H)
    (hsize : H ^ (((j + 3) * schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) + 1) ≤ N)
    {F : (ι → ℝ) → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hperiod : ∀ x : ι → ℝ, ∀ m : ι → ℤ, F (fun i => x i + m i) = F x) :
    ∃ q : ℕ, ∃ hq : 0 < q,
      q ≤ H ^ ((j + 3) * schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) ∧
      Fintype.card (Fin q × Fin (N / q / H + 1)) * H ≤ 2 * N ∧
      ∃ R : (Fin q × Fin (N / q / H + 1)) → ι → Polynomial ℝ,
        (∀ cell i, (R cell i).natDegree ≤ j) ∧
        ∀ n : Fin N,
          dist (F (fun i => (P i).eval (n.val : ℝ)))
            (F (fun i => (R (progressionBlockLabel q H hq n) i).eval
              ((n.val / q % H : ℕ) : ℝ))) ≤ (L : ℝ) / H := by
  obtain ⟨q, hq, hqbound, hfamily⟩ := hW.polynomial_progression_reduction P hP H hH hscale hF hperiod
  have hfit : q * H ≤ N := by
    calc
      _ ≤ H ^ ((j + 3) * schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) * H :=
        Nat.mul_le_mul_right H hqbound
      _ = H ^ (((j + 3) * schmidtRecurrenceExponent e * (Fintype.card ι + 1) ^ 2) + 1) :=
        (pow_succ _ _).symm
      _ ≤ N := hsize
  choose R hRdegree hRerror using
    (fun cell : Fin q × Fin (N / q / H + 1) => hfamily (progressionBlockStart cell : ℝ))
  refine ⟨q, hq, hqbound, progressionBlock_label_count_mul_le_twice hfit, R, hRdegree, ?_⟩
  intro n
  have hn : (n.val : ℝ) = (progressionBlockStart (progressionBlockLabel q H hq n) : ℝ) +
      (q : ℝ) * ((n.val / q % H : ℕ) : ℝ) := by
    exact_mod_cast (progressionBlock_reconstruct (H := H) hq n).symm
  have h := hRerror (progressionBlockLabel q H hq n) (n.val / q % H) (Nat.mod_lt _ hH)
  simpa only [← hn] using h

end Erdos3

end

end OAI
