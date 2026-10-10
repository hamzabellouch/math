import OAI.NumberTheory.TwoPoint.Bounds.ComplexBlockTesting

namespace OAI

/-! Normalize the actual directed block bound to the ordinary retained prefix. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma retainedComplexPrimeEdge_active_step_eq {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ)
    (e : ((j : Fin J) → P j) × Q) (n : ℤ) :
    retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n
      (n + retainedPrimeStep eligible h e) =
    retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n
      (n + (h * e.2.val * ∏ j, (e.1 j).val : ℕ)) := by
  by_cases he : eligible (∏ j, (e.1 j).val) e.2.val
  · rw [retainedPrimeStep, ite_eq_left he]
  · simp [retainedComplexPrimeEdge, retainedRealEdge, he]

noncomputable def retainedComplexPrefix {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ) (N : ℕ) : ℂ :=
  (positivePrefix (fun n => ∑ e : ((j : Fin J) → P j) × Q,
    retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n
      ((n : ℤ) + (h * e.2.val * ∏ j, (e.1 j).val : ℕ))) N / (N : ℂ)) / (L : ℂ)

theorem retainedComplexPrefix_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (M R N : ℕ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ)
    (hF : ∀ n, ‖F n‖ ≤ 1) (hG : ∀ n, ‖G n‖ ≤ 1)
    (hM : 0 < M) (hN : 0 < N) (hL : 0 < L) (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hu : ∀ q ∈ Q, 0 ≤ u q) (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hr : ∀ e : ((j : Fin J) → P j) × Q, retainedPrimeStep eligible h e ≤ R)
    (B : ℝ) (havg : uniformAverage (fun t : Fin N =>
      ‖retainedComplexBlock P M Q Qp u eligible L K W extra h gate keep F G t.val‖) ≤ B) :
    ‖retainedComplexPrefix P Q Qp u eligible L K W extra h gate keep F G N‖ ≤
      B / (L * M) + (R : ℝ) / M *
        (K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J) +
      2 * (M : ℝ) / N * (K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J) := by
  let C := K * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrow (n : ℕ) (_hn : 0 < n) :
      (∑ e : ((j : Fin J) → P j) × Q,
        ‖retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n
          ((n : ℤ) + retainedPrimeStep eligible h e)‖) ≤ C := by
    simp only [retainedComplexPrimeEdge_active_step_eq]
    exact retainedComplexPrimeEdge_row_bound P hprime hdisjoint Q Qp u eligible L K W
      extra h gate keep F G hF hG hL hK hW hu hV n
  have hb := retainedComplexBlock_prefix_bound P M R N Q Qp u eligible L K W extra h
    gate keep F G hM hN B C hC hr hrow havg
  simp only [retainedComplexPrimeEdge_active_step_eq] at hb
  unfold retainedComplexPrefix
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  apply (div_le_div_of_nonneg_right hb hL.le).trans
  dsimp [C]
  apply le_of_eq
  ring

end TwoPointCorrelations

end OAI
