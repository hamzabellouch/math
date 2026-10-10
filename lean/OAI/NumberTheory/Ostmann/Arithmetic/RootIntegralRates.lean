import OAI.NumberTheory.Ostmann.Arithmetic.RootMeshIntegral
import OAI.NumberTheory.Ostmann.Arithmetic.RootCellErrorRates

namespace OAI

/-! # Uniform rates for the whole sharp-gate integral -/

namespace Ostmann
open Filter MeasureTheory
open scoped BigOperators

theorem PublishedProgressionInput.root_integral_prime_rate (P : PublishedProgressionInput)
    (C : ℝ) (d K : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ Q q a : ℕ, 2 ≤ Q → 1 ≤ q → q ≤ Q → a.Coprime q →
      Real.log (4 * (Q : ℝ)) ≤ 2 * Real.exp ((12 / 1000 : ℝ) * L) →
      ∀ u v : ℝ, Real.exp ((49 / 1000 : ℝ) * L) ≤ u → u ≤ v → v ≤ u + 1 →
      ∀ (k : ℕ) (F : Fin k → ClippedPolynomialFactor) (S : Finset ℝ), S.card + 1 ≤ K →
      (∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S) →
      ∀ (w : ℝ → ℂ) (B : ℝ), 0 ≤ B → (∀ x, ‖w x‖ ≤ B) →
      (∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) →
      2 * B * smoothPolynomialBudget F ≤
        Real.exp (C * L ^ d + C * L * Real.exp ((12 / 1000 : ℝ) * L)) →
      ‖complexPrimeInterval q a u v (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
        ∫ y in Set.Ioc u v, w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) *
          (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
        Real.exp (-Real.exp ((125 / 10000 : ℝ) * L)) := by
  filter_upwards [P.root_cell_error_rate C d K, eventually_ge_atTop (0 : ℝ)] with L hL hL0
  intro Q q a hQ hq hqQ ha hlog u v hu huv hshort k F S hSK hroots w B hB hw hconst hbudget
  obtain ⟨s, N, hs, hs0, hsN, hN, hfree⟩ := finite_log_root_mesh S u v huv
  have hu1 : 1 ≤ s 0 := by rw [hs0]; exact (Real.one_le_exp (by positivity)).trans hu
  have h := P.common_root_prime_integral S s hs N hfree hQ hq hqQ ha hu1
    (by simpa only [hs0, hsN] using hshort) F hroots w B hB hw hconst
  rw [hs0, hsN] at h
  apply h.trans
  apply hL Q hQ hlog N (hN.trans hSK) s
    (fun j => ‖w (Real.exp ((s j + s (j + 1)) / 2))‖ * smoothPolynomialBudget F)
    (fun _ => 2 * B * smoothPolynomialBudget F)
  · intro j _
    exact hu.trans (by rw [← hs0]; exact hs (Nat.zero_le _))
  · intro j _
    have hbF := mul_le_mul_of_nonneg_right (hw (Real.exp ((s j + s (j + 1)) / 2)))
      (smoothPolynomialBudget_nonneg F)
    have hBF : 0 ≤ B * smoothPolynomialBudget F := mul_nonneg hB (smoothPolynomialBudget_nonneg F)
    nlinarith
  · intro j _
    exact hbudget

theorem root_integral_integer_bound (q a : ℕ) (hq : 0 < q) (u v G : ℝ) (huv : u ≤ v)
    {k : ℕ} (F : Fin k → ClippedPolynomialFactor) (S : Finset ℝ)
    (hroots : ∀ i r, r ∈ (F i).polynomial.derivative.roots → r ∈ S)
    (w : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ x, ‖w x‖ ≤ B)
    (hconst : ∀ x y, rootCellCode S x = rootCellCode S y → w x = w y) :
    ‖complexIntegerInterval q a u v G (fun y => w (Real.exp y) * smoothPolynomialWeight F (Real.exp y)) -
      ∫ y in Set.Ioc u v, w (Real.exp y) * smoothPolynomialWeight F (Real.exp y) *
        (integerLogDensity q G y : ℂ)‖ ≤
      4 * ((S.card + 1 : ℕ) : ℝ) * B * smoothPolynomialBudget F * Real.exp (-G) := by
  obtain ⟨s, N, hs, hs0, hsN, hN, hfree⟩ := finite_log_root_mesh S u v huv
  have h := common_root_integer_integral S s hs N hfree q a hq G F hroots w B hB hw hconst
  rw [hs0, hsN] at h
  apply h.trans
  calc
    _ ≤ ∑ _j ∈ Finset.range N, 4 * B * smoothPolynomialBudget F * Real.exp (-G) := by
      apply Finset.sum_le_sum
      intro j _
      have hbF := mul_le_mul_of_nonneg_right (hw (Real.exp ((s j + s (j + 1)) / 2)))
        (smoothPolynomialBudget_nonneg F)
      have he := mul_le_mul_of_nonneg_right hbF (by positivity : 0 ≤ 2 * Real.exp (-G))
      nlinarith
    _ = (N : ℝ) * (4 * B * smoothPolynomialBudget F * Real.exp (-G)) := by simp
    _ ≤ ((S.card + 1 : ℕ) : ℝ) * (4 * B * smoothPolynomialBudget F * Real.exp (-G)) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hN)
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hB)
        (smoothPolynomialBudget_nonneg F)) (Real.exp_pos _).le
    _ = _ := by ring

end Ostmann

end OAI
