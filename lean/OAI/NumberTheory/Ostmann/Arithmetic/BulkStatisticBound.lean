import OAI.NumberTheory.Ostmann.Arithmetic.SymmetrizedPairBound

namespace OAI

/-! # Finite assembly of the final bulk symmetrization estimate

The paired arithmetic estimates bound the constructed history amplitude.
-/

namespace Ostmann

open scoped BigOperators Classical

theorem bulkSymmetrize_energy_bound {A : Type*} [Fintype A] {r m : ℕ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) (μ : (Fin r × Fin m → A) → ℝ)
    (F : (Fin r × Fin m → A) → ℂ) (B E : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hpair : ∀ e f : Equiv.Perm (Fin r × Fin m),
      ‖∑ x, (μ x : ℂ) *
        (F (permuteBulk e x) * star (F (permuteBulk f x)))‖ ≤
        if BadBulkArrangement (e⁻¹ * f) then B else E) :
    (∑ x, μ x * ‖bulkSymmetrize F x‖ ^ 2) ≤
      ((r + 1) * r ^ (2 * r) : ℕ) *
        Real.exp ((r : ℝ) * m * (-(3 / 4 : ℝ) * Real.log r + 5 / 4)) * B + E := by
  have h := finiteFamilyAverage_good_bad_bound μ
    (fun e x => F (permuteBulk e x)) BadBulkArrangement B E hE hpair
  change (∑ x, μ x * ‖bulkSymmetrize F x‖ ^ 2) ≤ _ at h
  apply h.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ hB
  simpa only [card_bulkPerm] using badBulkArrangement_fraction_bound hr hm

theorem bulkSymmetrized_statistic_bound {A : Type*} [Fintype A] {r m : ℕ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (G F : (Fin r × Fin m → A) → ℂ)
    (hG : ∀ e x, G (permuteBulk e x) = G x)
    (R B E : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hregular : (∑ x, identicalBulkPrior μ x * ‖G x‖ ^ 2) ≤ R)
    (hpair : ∀ e f : Equiv.Perm (Fin r × Fin m),
      ‖∑ x, (identicalBulkPrior μ x : ℂ) *
        (F (permuteBulk e x) * star (F (permuteBulk f x)))‖ ≤
        if BadBulkArrangement (e⁻¹ * f) then B else E) :
    ‖∑ x, (identicalBulkPrior μ x : ℂ) * G x * F x‖ ^ 2 ≤
      R * (((r + 1) * r ^ (2 * r) : ℕ) *
        Real.exp ((r : ℝ) * m * (-(3 / 4 : ℝ) * Real.log r + 5 / 4)) * B + E) := by
  rw [← bulkSymmetrize_statistic μ G F hG]
  apply (bulkSymmetrize_cauchy μ hμ G F).trans
  exact mul_le_mul hregular
    (bulkSymmetrize_energy_bound hr hm (identicalBulkPrior μ) F B E hB hE hpair)
    (Finset.sum_nonneg fun x _ => mul_nonneg
      (Finset.prod_nonneg fun i _ => hμ (x i)) (sq_nonneg _)) hR

end Ostmann

end OAI
