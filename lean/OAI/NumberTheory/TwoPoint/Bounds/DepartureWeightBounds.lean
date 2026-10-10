import OAI.NumberTheory.TwoPoint.Bounds.CrudeTraceWeights

namespace OAI

/-! Bounds for the actual normalized departure factors after the cutoffs are discarded. -/

namespace TwoPointCorrelations

open Finset

noncomputable def departureWeight {r : ℕ} (L : ℝ) (u : ℕ → ℝ) (q : Fin r → ℕ)
    (denom cutoff : Fin r → ℝ) : ℝ :=
  ∏ i, (L * u (q i) / denom i) * cutoff i

lemma departureWeight_nonneg {r : ℕ} (L : ℝ) (u : ℕ → ℝ) (q : Fin r → ℕ)
    (denom cutoff : Fin r → ℝ) (hL : 0 ≤ L) (hu : ∀ i, 0 ≤ u (q i))
    (hd : ∀ i, 0 ≤ denom i) (hc : ∀ i, 0 ≤ cutoff i) :
    0 ≤ departureWeight L u q denom cutoff := by
  apply prod_nonneg
  intro i _
  exact mul_nonneg (div_nonneg (mul_nonneg hL (hu i)) (hd i)) (hc i)

lemma departureWeight_le_crude {r : ℕ} (L : ℝ) (u : ℕ → ℝ) (q : Fin r → ℕ)
    (denom cutoff : Fin r → ℝ) (hL : 0 ≤ L)
    (hu : ∀ i, 0 ≤ u (q i)) (hub : ∀ i, u (q i) ≤ crudePaddingWeight (q i))
    (hd : ∀ i, 1 ≤ denom i) (hc : ∀ i, 0 ≤ cutoff i) (hcb : ∀ i, cutoff i ≤ 1) :
    departureWeight L u q denom cutoff ≤ ∏ i, L * crudePaddingWeight (q i) := by
  apply prod_le_prod₀
  · intro i _
    exact mul_nonneg (div_nonneg (mul_nonneg hL (hu i)) (by linarith [hd i])) (hc i)
  · intro i _
    calc
      _ ≤ (L * u (q i) / denom i) * 1 :=
        mul_le_mul_of_nonneg_left (hcb i)
          (div_nonneg (mul_nonneg hL (hu i)) (by linarith [hd i]))
      _ = L * u (q i) / denom i := mul_one _
      _ ≤ L * u (q i) := div_le_self (mul_nonneg hL (hu i)) (hd i)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hub i) hL

/-- All designation and singleton multiplicities are included in this cost. -/
theorem departureWeight_designation_cost {r m S : ℕ}
    (L external Cexternal Csingle : ℝ) (u : ℕ → ℝ) (q : Fin r → ℕ)
    (denom cutoff : Fin r → ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hr : (r : ℝ) ≤ 2 * L)
    (hS : ((m + S : ℕ) : ℝ) ≤ Csingle * L * Real.log L)
    (hCe : 0 ≤ Cexternal) (he : 0 ≤ external)
    (hext : external ≤ Real.exp (Cexternal * L))
    (hpad : ∀ i, ((q i).primeFactors.card : ℝ) ≤ 100 * Real.log L)
    (hu : ∀ i, 0 ≤ u (q i)) (hub : ∀ i, u (q i) ≤ crudePaddingWeight (q i))
    (hd : ∀ i, 1 ≤ denom i) (hc : ∀ i, 0 ≤ cutoff i) (hcb : ∀ i, cutoff i ≤ 1) :
    (external * departureWeight L u q denom cutoff) * 2 ^ (m + S) ≤
      Real.exp ((Cexternal + Csingle + 402) * L * (Real.log L) ^ 2) := by
  apply le_trans _ (crudeTraceWeight_exp_bound r (m + S) q L external Cexternal Csingle
    hL hlog hr hS hCe hext hpad)
  calc
    _ ≤ (external * (∏ i, L * crudePaddingWeight (q i))) * 2 ^ (m + S) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (departureWeight_le_crude L u q denom cutoff (by linarith) hu hub hd hc hcb) he
    _ = crudeTraceWeight r (m + S) q L external := by
      unfold crudeTraceWeight
      ring

end TwoPointCorrelations

end OAI
