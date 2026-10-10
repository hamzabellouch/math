import OAI.Analysis.LipschitzHilbert.Phase.ImprovedFourthMoment

namespace OAI

/-! Finite mixed-norm comparisons for the diagonal Hilbert-valued extension. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem finite_minkowski (x : ι → κ → ℝ) (hx : ∀ i j, 0 ≤ x i j)
    {p : ℝ} (hp : 1 ≤ p) :
    (∑ j, (∑ i, x i j) ^ p) ^ (1 / p) ≤
      ∑ i, (∑ j, x i j ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have h (s : Finset ι) : (∑ j, (∑ i ∈ s, x i j) ^ p) ^ (1 / p) ≤
      ∑ i ∈ s, (∑ j, x i j ^ p) ^ (1 / p) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      have hm := Real.Lp_add_le_of_nonneg (Finset.univ : Finset κ)
        (f := fun j => x i j) (g := fun j => ∑ k ∈ s, x k j) hp
        (fun j _ => hx i j) (fun j _ => Finset.sum_nonneg (fun k _ => hx k j))
      exact hm.trans (add_le_add le_rfl ih)
  exact h Finset.univ

/-- Interchanging the finite `ℓ^r` and `ℓ²` norms costs no constant when `r ≤ 2`. -/
theorem mixed_norm_comparison (x : ι → κ → ℝ) (hx : ∀ i j, 0 ≤ x i j)
    {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    (∑ j, (∑ i, x i j ^ r) ^ (2 / r)) ≤
      (∑ i, (∑ j, x i j ^ 2) ^ (r / 2)) ^ (2 / r) := by
  have hm := finite_minkowski (fun i j => x i j ^ r)
    (fun i j => Real.rpow_nonneg (hx i j) r)
    ((le_div_iff₀ hr).2 (by simpa using hr2))
  have heq (i : ι) (j : κ) : (x i j ^ r) ^ (2 / r) = x i j ^ (2 : ℕ) := by
    rw [← Real.rpow_mul (hx i j)]
    have he : r * (2 / r) = 2 := by field_simp
    rw [he, Real.rpow_ofNat]
  simp only [heq, one_div_div] at hm
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg
    (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg
      (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx i j) r)) _)) _) hm
    (show 0 ≤ 2 / r by positivity)
  rw [← Real.rpow_mul (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx i j) r)) _))] at hpow
  have hcancel : r / 2 * (2 / r) = 1 := by field_simp
  simpa only [hcancel, Real.rpow_one] using hpow

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
