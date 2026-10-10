import Mathlib.Analysis.Normed.Group.Bounded
import OAI.NumberTheory.Ostmann.Supply.PrimePowerTransferBasic

namespace OAI

noncomputable section
namespace Ostmann.Supply
open Finset Set Ostmann.ZeroDensity
open scoped BigOperators Topology

def totalPrimitivePrimeError (Q : ℕ) (exception : Option (PrimitiveFamily Q))
    (φ : ℝ → ℝ) (X : ℝ) : ℝ :=
  ∑ χ : PrimitiveFamily Q, if some χ = exception then 0 else ‖smoothPrimeError χ.2.1 φ X‖

theorem exists_primePower_transfer_constant (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (X : ℝ), 0 < X →
      ‖smoothError χ φ X-smoothPrimeError χ φ X‖ ≤ C*Real.sqrt X := by
  have hc : HasCompactSupport φ :=
    HasCompactSupport.of_support_subset_isCompact (K := Icc (1/2 : ℝ) 1) isCompact_Icc
      (fun x hx => ⟨(hs (subset_tsupport φ hx)).1.le, (hs (subset_tsupport φ hx)).2.le⟩)
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hφ
  obtain ⟨D, hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨(|B|+1)*(|D|+1), by positivity, ?_⟩
  intro q _ χ X hX
  have htest : ∀ x, ‖φ x‖ ≤ |B|+1 := fun x =>
    (hB x).trans (by linarith [le_abs_self B])
  calc
    _ ≤ (|B|+1)*(Chebyshev.psi X-Chebyshev.theta X) :=
      norm_smoothError_sub_smoothPrimeError_le χ hs hX htest
    _ ≤ (|B|+1)*(D*Real.sqrt X) :=
      mul_le_mul_of_nonneg_left (hD X) (by positivity)
    _ ≤ (|B|+1)*((|D|+1)*Real.sqrt X) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self D]) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem totalPrimitivePrimeError_le (Q : ℕ) (exception : Option (PrimitiveFamily Q))
    (φ : ℝ → ℝ) (X E : ℝ) (hE : 0 ≤ E)
    (h : ∀ χ : PrimitiveFamily Q, ‖smoothError χ.2.1 φ X-smoothPrimeError χ.2.1 φ X‖ ≤ E) :
    totalPrimitivePrimeError Q exception φ X ≤ totalPrimitiveError Q exception φ X+(Q : ℝ)^2*E := by
  calc
    _ ≤ ∑ χ : PrimitiveFamily Q,
        ((if some χ = exception then 0 else ‖smoothError χ.2.1 φ X‖)+E) := by
      apply sum_le_sum
      intro χ hχ
      by_cases he : some χ = exception
      · simpa only [ite_eq_left he, zero_add] using hE
      · simp only [ite_eq_right he]
        calc
          _ = ‖smoothError χ.2.1 φ X-(smoothError χ.2.1 φ X-smoothPrimeError χ.2.1 φ X)‖ := by
            rw [sub_sub_cancel]
          _ ≤ ‖smoothError χ.2.1 φ X‖+‖smoothError χ.2.1 φ X-smoothPrimeError χ.2.1 φ X‖ :=
            norm_sub_le _ _
          _ ≤ _ := add_le_add le_rfl (h χ)
    _ = totalPrimitiveError Q exception φ X+(Fintype.card (PrimitiveFamily Q) : ℝ)*E := by
      simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, totalPrimitiveError]
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right _ hE
      exact_mod_cast card_primitiveFamily_le Q

theorem exists_totalPrimitivePrimeError_le (φ : ℝ → ℝ) (hφ : Continuous φ)
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) (exception : Option (PrimitiveFamily Q)) (X : ℝ), 0 < X →
      totalPrimitivePrimeError Q exception φ X ≤ totalPrimitiveError Q exception φ X+
        (Q : ℝ)^2*C*Real.sqrt X := by
  obtain ⟨C, hC, h⟩ := exists_primePower_transfer_constant φ hφ hs
  refine ⟨C, hC, ?_⟩
  intro Q exception X hX
  have hb := totalPrimitivePrimeError_le Q exception φ X (C*Real.sqrt X)
    (mul_nonneg hC.le (Real.sqrt_nonneg _)) (fun χ => h (χ.1.val+1) χ.2.1 X hX)
  simpa only [mul_assoc] using hb

end Ostmann.Supply

end

end OAI
