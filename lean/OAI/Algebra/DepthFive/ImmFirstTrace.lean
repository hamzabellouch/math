import OAI.Algebra.DepthFive.ImmFiniteMatrix
import OAI.Algebra.DepthFive.FirstTraceNonnegative

namespace OAI

noncomputable section
open scoped BigOperators Matrix

namespace Problem335

/-- The real, nonnegative matrix underlying the actual normalized IMM map. -/
def immRealNormalizedMatrix (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ) :
    Matrix (ImmTargetIndex n side a b) (ImmSourceIndex n side a b) ℝ := by
  classical
  exact fun e d => ∑ p : Fin (immPaths n hn).length,
    if immPathOccupation n hn (fun x => side x.1) d.1 p = e.1
    then immPathAmplitude n hn (fun x => side x.1) d.1 p else 0

theorem immNormalizedMatrix_eq_map_real (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ) :
    immNormalizedMatrix n side a b =
      (immRealNormalizedMatrix n hn side a b).map Complex.ofReal := by
  classical
  ext e d
  rw [immNormalizedMatrix_apply n hn]
  simp only [Matrix.map_apply, immRealNormalizedMatrix, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

/-- Every nonzero path amplitude occurs in exactly one genuine target row.
Zero-amplitude paths need no artificial target-row choice. -/
theorem immPathAmplitude_sq_sum_target (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ) (d : ImmSourceIndex n side a b)
    (p : Fin (immPaths n hn).length) :
    (∑ e : ImmTargetIndex n side a b,
      (if immPathOccupation n hn (fun x => side x.1) d.1 p = e.1
       then immPathAmplitude n hn (fun x => side x.1) d.1 p else 0) ^ 2) =
      immPathAmplitude n hn (fun x => side x.1) d.1 p ^ 2 := by
  classical
  by_cases hw : immPathAmplitude n hn (fun x => side x.1) d.1 p = 0
  · simp [hw]
  let e : ImmTargetIndex n side a b :=
    ⟨immPathOccupation n hn (fun x => side x.1) d.1 p,
      immPathOccupation_bidegree_of_amplitude_ne_zero n hn side a b d.1 d.2 p hw⟩
  rw [Finset.sum_eq_single e]
  · simp [e]
  · intro e' he' hne
    have hocc : immPathOccupation n hn (fun x => side x.1) d.1 p ≠ e'.1 := by
      intro heq
      apply hne
      exact Subtype.ext heq.symm
    simp [hocc]
  · simp

/-- Actual normalized IMM first trace dominates the total occupation mass.
Nonnegative coefficients make path-collision analysis unnecessary for this
lower bound. All sources and targets are the genuine finite bidegree spaces. -/
theorem immNormalizedMatrix_first_trace_lower (n : ℕ) (hn : 0 < n)
    (side : Fin n → Bool) (a b : ℕ) :
    (∑ d : ImmSourceIndex n side a b, ∑ p : Fin (immPaths n hn).length,
      immPathAmplitude n hn (fun x => side x.1) d.1 p ^ 2) ≤
      ((immNormalizedMatrix n side a b).conjTranspose *
        immNormalizedMatrix n side a b).trace.re := by
  classical
  rw [immNormalizedMatrix_eq_map_real n hn, complexify_first_trace,
    trace_transpose_mul_self]
  apply Finset.sum_le_sum
  intro d hd
  calc
    _ = ∑ p : Fin (immPaths n hn).length, ∑ e : ImmTargetIndex n side a b,
        (if immPathOccupation n hn (fun x => side x.1) d.1 p = e.1
         then immPathAmplitude n hn (fun x => side x.1) d.1 p else 0) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (immPathAmplitude_sq_sum_target n hn side a b d p).symm
    _ = ∑ e : ImmTargetIndex n side a b, ∑ p : Fin (immPaths n hn).length,
        (if immPathOccupation n hn (fun x => side x.1) d.1 p = e.1
         then immPathAmplitude n hn (fun x => side x.1) d.1 p else 0) ^ 2 :=
      Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_sq_le_sq_sum_of_nonneg
      intro p hp
      split_ifs
      · exact immPathAmplitude_nonneg n hn _ d.1 p
      · exact le_rfl

/-- Uniform actual-source occupation averages lift to the normalized IMM
first trace with exactly `n^(n-1)` endpoint paths. -/
theorem immNormalizedMatrix_first_trace_lower_of_average
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ) (L : ℝ)
    (hmean : ∀ p : Fin (immPaths n hn).length,
      L ≤ (∑ d : ImmSourceIndex n side a b,
        immPathAmplitude n hn (fun x => side x.1) d.1 p ^ 2) /
          (Fintype.card (ImmSourceIndex n side a b) : ℝ)) :
    (Fintype.card (ImmSourceIndex n side a b) : ℝ) * (n : ℝ) ^ (n - 1) * L ≤
      ((immNormalizedMatrix n side a b).conjTranspose *
        immNormalizedMatrix n side a b).trace.re := by
  classical
  have hsum (p : Fin (immPaths n hn).length) :
      (Fintype.card (ImmSourceIndex n side a b) : ℝ) * L ≤
        ∑ d : ImmSourceIndex n side a b,
          immPathAmplitude n hn (fun x => side x.1) d.1 p ^ 2 := by
    by_cases hz : Fintype.card (ImmSourceIndex n side a b) = 0
    · simp only [hz, Nat.cast_zero, zero_mul]
      exact Finset.sum_nonneg (fun d _ => sq_nonneg _)
    · have hpos : (0 : ℝ) < Fintype.card (ImmSourceIndex n side a b) := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      simpa only [mul_comm] using (le_div_iff₀ hpos).mp (hmean p)
  calc
    _ = ∑ p : Fin (immPaths n hn).length,
        (Fintype.card (ImmSourceIndex n side a b) : ℝ) * L := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        immPaths_length, nsmul_eq_mul, Nat.cast_pow]
      ring
    _ ≤ ∑ p : Fin (immPaths n hn).length, ∑ d : ImmSourceIndex n side a b,
        immPathAmplitude n hn (fun x => side x.1) d.1 p ^ 2 :=
      Finset.sum_le_sum (fun p _ => hsum p)
    _ = ∑ d : ImmSourceIndex n side a b, ∑ p : Fin (immPaths n hn).length,
        immPathAmplitude n hn (fun x => side x.1) d.1 p ^ 2 := Finset.sum_comm
    _ ≤ _ := immNormalizedMatrix_first_trace_lower n hn side a b

end Problem335

end

end OAI
