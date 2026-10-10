import OAI.NumberTheory.CubicMoment.Estimates.GramOperator

namespace OAI

/-!
# A smooth majorant in the Gram bound

The majorant needs to be at least one only on the coefficient support.
It may vanish elsewhere. This is the weighted Cauchy step used to pass
from smooth character Gram estimates to finite Dirichlet polynomials.
-/

noncomputable section
open scoped BigOperators

namespace CubicFirstMoment

def weightedFiniteGram {ι κ : Type*} (N : Finset κ) (w : κ → ℝ)
    (T : ι → κ → ℂ) (p q : ι) : ℂ :=
  ∑ n ∈ N, (w n : ℂ) * T p n * star (T q n)

theorem weightedFiniteGram_eq {ι κ : Type*} (N : Finset κ) (w : κ → ℝ)
    (T : ι → κ → ℂ) (hw : ∀ n ∈ N, 0 ≤ w n) (p q : ι) :
    weightedFiniteGram N w T p q =
      finiteGram N (fun p n => (Real.sqrt (w n) : ℂ) * T p n) p q := by
  unfold weightedFiniteGram finiteGram
  apply Finset.sum_congr rfl
  intro n hn
  have he : (Real.sqrt (w n) : ℂ)^2 = (w n : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (hw n hn)
  have hs : star (Real.sqrt (w n) : ℂ) = (Real.sqrt (w n) : ℂ) :=
    Complex.conj_ofReal _
  simp only [star_mul, hs]
  linear_combination - T p n * star (T q n) * he

/-- The Gram row bound controls coefficients beneath any nonnegative
smooth majorant which is at least one on their support. -/
theorem weighted_gram_operator_le {ι κ : Type*} (P : Finset ι) (N : Finset κ)
    (v : κ → ℂ) (T : ι → κ → ℂ) (w : κ → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hw : ∀ n ∈ N, 0 ≤ w n) (hv : ∀ n ∈ N, v n ≠ 0 → 1 ≤ w n)
    (hrow : ∀ p ∈ P, ∑ q ∈ P, ‖weightedFiniteGram N w T p q‖ ≤ R) :
    (∑ p ∈ P, ‖∑ n ∈ N, v n * T p n‖^2) ≤ R * ∑ n ∈ N, ‖v n‖^2 := by
  let v' : κ → ℂ := fun n => v n / (Real.sqrt (w n) : ℂ)
  let T' : ι → κ → ℂ := fun p n => (Real.sqrt (w n) : ℂ) * T p n
  have hroot (n : κ) (hn : n ∈ N) (hv0 : v n ≠ 0) : 1 ≤ Real.sqrt (w n) := by
    exact Real.one_le_sqrt.mpr (hv n hn hv0)
  have hsame (p : ι) : (∑ n ∈ N, v' n * T' p n) = ∑ n ∈ N, v n * T p n := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hv0 : v n = 0
    · simp [v', T', hv0]
    · have hr : (Real.sqrt (w n) : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (hroot n hn hv0)))
      dsimp [v', T']
      field_simp
  have henergy : (∑ n ∈ N, ‖v' n‖^2) ≤ ∑ n ∈ N, ‖v n‖^2 := by
    apply Finset.sum_le_sum
    intro n hn
    by_cases hv0 : v n = 0
    · simp [v', hv0]
    · apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
      dsimp [v']
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact div_le_self (_root_.norm_nonneg _) (hroot n hn hv0)
  have hr : ∀ p ∈ P, ∑ q ∈ P, ‖finiteGram N T' p q‖ ≤ R := by
    intro p hp
    simpa only [T', ← weightedFiniteGram_eq N w T hw] using hrow p hp
  have h := finite_gram_operator_le P N v' T' hR hr
  simp only [hsame] at h
  exact h.trans (mul_le_mul_of_nonneg_left henergy hR)

end CubicFirstMoment

end

end OAI
