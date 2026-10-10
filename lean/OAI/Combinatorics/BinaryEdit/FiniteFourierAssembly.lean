import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Assembly of the finite-group displacement identity

Summing finite cut representations and the Parseval identities for cut
indicators gives the finite-group displacement identity.
-/

noncomputable section

open scoped BigOperators

namespace TreeEdit.BinaryLower

/-- Summing nonnegative spectral weights with nonnegative cut coefficients
preserves nonnegativity. -/
theorem cut_spectral_weight_nonneg {C K : Type*} [Fintype C]
    (a : C → ℝ) (b : C → K → ℝ)
    (ha : ∀ c, 0 ≤ a c) (hb : ∀ c k, 0 ≤ b c k) (k : K) :
    0 ≤ ∑ c, a c * b c k := by
  exact Finset.sum_nonneg fun c _ => mul_nonneg (ha c) (hb c k)

/-- Interchange a finite cut sum and a finite spectral sum. -/
theorem sum_cut_spectral_weights {C K : Type*} [Fintype C] [Fintype K]
    (a : C → ℝ) (b : C → K → ℝ) (multiplier : K → ℝ) :
    (∑ c, a c * ∑ k, multiplier k * b c k) =
      ∑ k, multiplier k * ∑ c, a c * b c k := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- A finite cut expansion together with the spectral expansion of each cut
implies the averaged displacement representation.  Neither injectivity of
`F` nor nontriviality of the individual cuts is needed. -/
theorem finite_fourier_of_cut_expansions
    {A C E : Type*} [AddCommGroup A] [Fintype A] [Fintype C]
    [NormedAddCommGroup E]
    (F : A → E) (a : C → ℝ) (U : C → A → ℝ)
    (b : C → AddChar A ℂ → ℝ)
    (ha : ∀ c, 0 ≤ a c) (hb : ∀ c χ, 0 ≤ b c χ)
    (hcut : ∀ x y, ‖F x - F y‖ = ∑ c, a c * |U c x - U c y|)
    (hfourier : ∀ c z,
      (𝔼 x, |U c (x + z) - U c x|) =
        ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * b c χ) :
    ∃ H : AddChar A ℂ → ℝ, (∀ χ, 0 ≤ H χ) ∧
      ∀ z, (𝔼 x, ‖F (x + z) - F x‖) =
        ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * H χ := by
  classical
  refine ⟨fun χ => ∑ c, a c * b c χ,
    cut_spectral_weight_nonneg a b ha hb, ?_⟩
  intro z
  calc
    (𝔼 x, ‖F (x + z) - F x‖) =
        𝔼 x, ∑ c, a c * |U c (x + z) - U c x| := by
          apply Finset.expect_congr rfl
          intro x _
          exact hcut (x + z) x
    _ = ∑ c, a c * (𝔼 x, |U c (x + z) - U c x|) := by
          rw [Finset.expect_sum_comm]
          apply Finset.sum_congr rfl
          intro c _
          exact (Finset.mul_expect _ _ _).symm
    _ = ∑ c, a c * ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * b c χ := by
          simp_rw [hfourier]
    _ = ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * ∑ c, a c * b c χ :=
          sum_cut_spectral_weights a b (fun χ => ‖1 - χ z‖ ^ 2)

/-- Every character displacement multiplier is nonnegative. -/
theorem character_displacement_nonneg {A : Type*} [AddCommGroup A]
    (χ : AddChar A ℂ) (z : A) : 0 ≤ ‖1 - χ z‖ ^ 2 := sq_nonneg _

/-- The multiplier bound used in the finite root-mass estimate. -/
theorem character_displacement_le_four {A : Type*} [AddCommGroup A] [Finite A]
    (χ : AddChar A ℂ) (z : A) : ‖1 - χ z‖ ^ 2 ≤ 4 := by
  have h : ‖1 - χ z‖ ≤ 2 := by
    calc
      ‖1 - χ z‖ ≤ ‖(1 : ℂ)‖ + ‖χ z‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_one, χ.norm_apply]; norm_num
  have hnn := norm_nonneg (1 - χ z)
  nlinarith

/-- Root-inactive characters have zero multiplier, and only those characters do. -/
theorem character_displacement_eq_zero_iff {A : Type*} [AddCommGroup A]
    (χ : AddChar A ℂ) (z : A) : ‖1 - χ z‖ ^ 2 = 0 ↔ χ z = 1 := by
  rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero, eq_comm]

end TreeEdit.BinaryLower

end

end OAI
