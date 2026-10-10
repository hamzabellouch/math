import OAI.Analysis.KadisonKastler.ScalarPullbackAlgebra
import OAI.Analysis.KadisonKastler.AbelianCesaro

namespace OAI

/-! # Contractive Cesaro averages for the nonsingular boundary shift -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [MeasurableSpace D] {μ : Measure D} [IsFiniteMeasure μ]
  (S : D → D) (hS : Measure.QuasiMeasurePreserving S μ μ)

def scalarShiftCesaro (n : ℕ) : ScalarLInfinity μ →L[ℂ] ScalarLInfinity μ :=
  (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) •
    ∑ i ∈ Finset.range (n + 1), (scalarInfinityPullbackL S hS) ^ i

theorem scalarShiftCesaro_apply (n : ℕ) (f : ScalarLInfinity μ) :
    scalarShiftCesaro S hS n f = (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) •
      ∑ i ∈ Finset.range (n + 1), ((scalarInfinityPullbackL S hS) ^ i) f := by
  simp only [scalarShiftCesaro, smul_apply, sum_apply]

theorem scalarPullback_power_norm_le (n : ℕ) (f : ScalarLInfinity μ) :
    ‖((scalarInfinityPullbackL S hS) ^ n) f‖ ≤ ‖f‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact (norm_scalarInfinityPullback_le S hS _).trans ih

theorem scalarShiftCesaro_norm_le (n : ℕ) (f : ScalarLInfinity μ) :
    ‖scalarShiftCesaro S hS n f‖ ≤ ‖f‖ := by
  have hp : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  simp only [scalarShiftCesaro, smul_apply, sum_apply]
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (n + 1))]
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i ∈ Finset.range (n + 1),
        ‖((scalarInfinityPullbackL S hS) ^ i) f‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ _i ∈ Finset.range (n + 1), ‖f‖ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun i _ => scalarPullback_power_norm_le S hS i f)
    _ = ‖f‖ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

theorem scalarShiftCesaro_difference (n : ℕ) (f : ScalarLInfinity μ) :
    scalarInfinityPullbackL S hS (scalarShiftCesaro S hS n f) - scalarShiftCesaro S hS n f =
      (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) •
        (((scalarInfinityPullbackL S hS) ^ (n + 1)) f - f) := by
  let U := scalarInfinityPullbackL S hS
  have hp (i : ℕ) : U ((U ^ i) f) = (U ^ (i + 1)) f :=
    congrArg (fun A : ScalarLInfinity μ →L[ℂ] ScalarLInfinity μ => A f) (pow_succ' U i).symm
  simp only [scalarShiftCesaro, smul_apply, sum_apply,
    map_smul, map_sum, ← smul_sub, ← Finset.sum_sub_distrib]
  change _ = (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) • ((U ^ (n + 1)) f - f)
  congr 1
  simp_rw [show ∀ i, scalarInfinityPullbackL S hS
      (((scalarInfinityPullbackL S hS) ^ i) f) = (U ^ (i + 1)) f from hp]
  simpa using Finset.sum_range_sub (fun i : ℕ => (U ^ i) f) (n + 1)

theorem scalarShiftCesaro_difference_norm_le (n : ℕ) (f : ScalarLInfinity μ) :
    ‖scalarInfinityPullbackL S hS (scalarShiftCesaro S hS n f) - scalarShiftCesaro S hS n f‖ ≤
      2 * ((n + 1 : ℕ) : ℝ)⁻¹ * ‖f‖ := by
  rw [scalarShiftCesaro_difference]
  exact norm_inv_nat_smul_sub_le n _ f (scalarPullback_power_norm_le S hS (n + 1) f)

theorem scalarShiftCesaro_fixed (n : ℕ) (f : ScalarLInfinity μ)
    (hf : scalarInfinityPullback S hS f = f) : scalarShiftCesaro S hS n f = f := by
  have hp (i : ℕ) : ((scalarInfinityPullbackL S hS) ^ i) f = f := by
    induction i with
    | zero => simp
    | succ i hi =>
      rw [pow_succ', mul_apply_eq_comp, hi]
      exact hf
  simp only [scalarShiftCesaro, smul_apply, sum_apply, hp, Finset.sum_const, Finset.card_range]
  have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  change (((n + 1 : ℕ) : ℂ)⁻¹ * ((n + 1 : ℕ) : ℂ)) • f = f
  rw [inv_mul_cancel₀ hn, one_smul]

end

end KadisonKastler

end OAI
