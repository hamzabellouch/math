import OAI.NumberTheory.Ostmann.Arithmetic.FiniteRootMesh
import OAI.NumberTheory.Ostmann.Arithmetic.OpenCellPrimeComparison
import OAI.NumberTheory.Ostmann.ZeroDensity.RootFreeSmoothWeight

namespace OAI

/-! # Weighted prime comparison for the complete finite root-cell multiplier -/

namespace Ostmann
open scoped BigOperators Classical
open MeasureTheory

/-- Root-cell multipliers include the exact sharp arithmetic indicators.
The continuous factors and all endpoint primes are retained. -/
theorem PublishedProgressionInput.root_cell_prime_comparison (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    {n : ℕ} (F : Fin n → ClippedPolynomialFactor)
    (S : Finset ℝ) (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (c : (S → Ordering) → ℂ) (C : ℝ) (hC : 0 ≤ C) (hc : ∀ code, ‖c code‖ ≤ C) :
    ∃ (s : ℕ → ℝ) (N : ℕ) (d : ℕ → ℂ),
      Monotone s ∧ s 0 = u ∧ s N = v ∧ N ≤ S.card + 1 ∧ (∀ j, ‖d j‖ ≤ C) ∧
      ‖complexPrimeInterval q a u v
          (fun y => c (rootCellCode S (Real.exp y)) * smoothPolynomialWeight F (Real.exp y)) -
        ∑ j ∈ Finset.range N, ∫ y in Set.Ioc (s j) (s (j + 1)),
          d j * smoothPolynomialWeight F (Real.exp y) *
            (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
        ∑ j ∈ Finset.range N,
          (‖d j‖ * smoothPolynomialBudget F *
            (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt (s j)) +
              Real.exp (-P.kappa * s j / Real.log (4 * (Q : ℝ)))) +
            2 * C * smoothPolynomialBudget F * Real.exp (-(s j))) := by
  obtain ⟨s, N, hs, hs0, hsN, hN, hfree⟩ := finite_log_root_mesh S u v huv
  let d := fun j => c (rootCellCode S (Real.exp ((s j + s (j + 1)) / 2)))
  have hd (j : ℕ) : ‖d j‖ ≤ C := hc _
  refine ⟨s, N, d, hs, hs0, hsN, hN, hd, ?_⟩
  rw [← hs0, ← hsN]
  apply P.piecewise_prime_comparison hQ hq hqQ ha s hs N (by simpa only [hs0] using hu)
    (by simpa only [hs0, hsN] using hshort)
    _ (fun j y => d j * smoothPolynomialWeight F (Real.exp y))
    (fun j => ‖d j‖ * smoothPolynomialBudget F)
    (fun _ => 2 * C * smoothPolynomialBudget F)
  · intro j hj
    exact continuousOn_const.mul
      (((continuous_smoothPolynomialWeight F).comp Real.continuous_exp).continuousOn)
  · intro j hj r hr M hr0 hrM
    rw [discreteVariation_const_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply smoothPolynomialWeight_variation_no_roots F (fun k => Real.exp (r k))
      (Real.exp_monotone.comp hr) M
    intro i x hx hxin
    apply hfree j hj x (hroots i x hx)
    refine ⟨?_, ?_⟩
    · simpa only [hr0] using hxin.1
    · have hlast : Real.exp (r (M - 1)) ≤ Real.exp (s (j + 1)) := by
        rw [← hrM]
        exact Real.exp_le_exp.mpr (hr (Nat.sub_le M 1))
      exact hxin.2.trans_le hlast
  · intro j hj
    exact mul_nonneg (mul_nonneg (by positivity) hC) (smoothPolynomialBudget_nonneg F)
  · intro j hj y hy
    calc
      _ ≤ ‖c (rootCellCode S (Real.exp y)) * smoothPolynomialWeight F (Real.exp y)‖ +
          ‖d j * smoothPolynomialWeight F (Real.exp y)‖ := norm_sub_le _ _
      _ ≤ C * smoothPolynomialBudget F + C * smoothPolynomialBudget F := by
        simp only [norm_mul]
        exact add_le_add
          (mul_le_mul (hc _) (smoothPolynomialWeight_norm F _) (norm_nonneg _) hC)
          (mul_le_mul (hd _) (smoothPolynomialWeight_norm F _) (norm_nonneg _) hC)
      _ = _ := by ring
  · intro j hj y hy
    congr 2
    apply rootCellCode_eq_of_root_free S (Real.exp (s j)) (Real.exp (s (j + 1)))
      (Real.exp y) (Real.exp ((s j + s (j + 1)) / 2)) (hfree j hj)
    · exact ⟨Real.exp_lt_exp.mpr hy.1, Real.exp_lt_exp.mpr hy.2⟩
    · constructor <;> apply Real.exp_lt_exp.mpr <;> linarith [hy.1, hy.2]

end Ostmann

end OAI
