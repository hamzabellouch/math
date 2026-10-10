import OAI.NumberTheory.CubicMoment.Estimates.HeckeSymmetry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.SpecificCodomains.Pi

namespace OAI

/-! A common scalar majorant permits integration before the finite
character square-sum. The conductor and root number remain row scalars. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace CubicFirstMoment

theorem common_majorant_square_sum {ι : Type*} [Fintype ι]
    (F : ι → ℝ → ℂ) (w : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ i, Integrable (F i)) (hw : Integrable w)
    (hw0 : ∀ τ, 0 ≤ w τ)
    (hbound : ∀ τ, (∑ i, ‖F i τ‖^2) ≤ (w τ)^2*B) :
    (∑ i, ‖∫ τ : ℝ, F i τ‖^2) ≤ (∫ τ : ℝ, w τ)^2*B := by
  let v : ℝ → EuclideanSpace ℂ ι := fun τ => WithLp.toLp 2 (fun i => F i τ)
  have hpi : Integrable (fun τ => fun i => F i τ) := Integrable.of_eval hF
  have hv : Integrable v :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℂ)).symm.toContinuousLinearMap.integrable_comp hpi
  have hnorm (τ : ℝ) : ‖v τ‖ ≤ w τ * Real.sqrt B := by
    have he : ‖v τ‖^2 = ∑ i, ‖F i τ‖^2 := EuclideanSpace.norm_sq_eq (v τ)
    apply (sq_le_sq₀ (_root_.norm_nonneg _) (mul_nonneg (hw0 τ) (Real.sqrt_nonneg _))).mp
    rw [he,mul_pow,Real.sq_sqrt hB]
    exact hbound τ
  have hint : ‖∫ τ : ℝ, v τ‖ ≤ (∫ τ : ℝ, w τ)*Real.sqrt B := by
    calc
      _ ≤ ∫ τ : ℝ, ‖v τ‖ := norm_integral_le_integral_norm v
      _ ≤ ∫ τ : ℝ, w τ*Real.sqrt B := integral_mono hv.norm (hw.mul_const _) hnorm
      _ = _ := integral_mul_const _ _
  have hcoord (i : ι) : (∫ τ : ℝ, v τ) i = ∫ τ : ℝ, F i τ := by
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℂ) i).integral_comp_comm hv).symm
  have he : ‖∫ τ : ℝ, v τ‖^2 = ∑ i, ‖∫ τ : ℝ, F i τ‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hcoord]
  have hsq := pow_le_pow_left₀ (_root_.norm_nonneg _) hint 2
  rw [he,mul_pow,Real.sq_sqrt hB] at hsq
  exact hsq

/-- A simultaneous character average can use one norm-shift measure:
the conductor-dependent Hecke factor contributes exactly no loss. -/
theorem hecke_common_majorant_square_sum {ι : Type*} [Fintype ι]
    (ε : ι → ℂ) (D : ι → ℝ) (Z k t : ℝ) (P W : ι → ℝ → ℂ)
    (w : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hε : ∀ i, ‖ε i‖ = 1) (hk : 0 ≤ k)
    (hInt : ∀ i, Integrable (fun τ =>
      W i τ * heckeSymmetryFactor (ε i) (D i) Z k t τ * P i τ))
    (hw : Integrable w) (hw0 : ∀ τ, 0 ≤ w τ)
    (hW : ∀ i τ, ‖W i τ‖ ≤ w τ)
    (hP : ∀ τ, (∑ i, ‖P i τ‖^2) ≤ B) :
    (∑ i, ‖∫ τ : ℝ,
      W i τ * heckeSymmetryFactor (ε i) (D i) Z k t τ * P i τ‖^2) ≤
        (∫ τ : ℝ, w τ)^2*B := by
  apply common_majorant_square_sum _ w hB hInt hw hw0
  intro τ
  calc
    _ = ∑ i, ‖W i τ‖^2 * ‖P i τ‖^2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_mul,norm_mul,norm_heckeSymmetryFactor (hε i) _ _ _ _ _ hk,mul_one,mul_pow]
    _ ≤ ∑ i, (w τ)^2 * ‖P i τ‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (_root_.norm_nonneg _) (hW i τ) 2) (sq_nonneg _)
    _ = (w τ)^2 * ∑ i, ‖P i τ‖^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hP τ) (sq_nonneg _)

end CubicFirstMoment

end

end OAI
