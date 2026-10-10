import OAI.NumberTheory.Ostmann.Characters.AffineOperator
import OAI.NumberTheory.Ostmann.Preliminaries.FiniteMean

namespace OAI

/-!
# Constant and mean-zero parts of the affine average

The self-correlation estimate here is the operator inequality used to
prove the uniform Mellin estimate in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem fieldMean_eq_sum {p : ℕ} [NeZero p] (F : ZMod p → ℂ) :
    fieldMean F = (p : ℂ)⁻¹ * ∑ t : ZMod p, F t := by
  rw [fieldMean, additiveFourier, ZMod.dft_apply_zero]

noncomputable def unitMean {p : ℕ} [Fact p.Prime] (W : (ZMod p)ˣ → ℂ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ r : (ZMod p)ˣ, W r

theorem affineAverage_mean {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) :
    fieldMean (affineAverage W F) = unitMean W * fieldMean F := by
  have hreindex (r : (ZMod p)ˣ) : (∑ t : ZMod p, F (affineGenerator r t)) =
      ∑ t : ZMod p, F t := (affineGeneratorEquiv r).bijective.sum_comp F
  rw [fieldMean_eq_sum, fieldMean_eq_sum]
  calc
    _ = (p : ℂ)⁻¹ ^ 2 * ∑ r : (ZMod p)ˣ,
        W r * ∑ t : ZMod p, F (affineGenerator r t) := by
      simp only [affineAverage, Finset.mul_sum, pow_two, mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [hreindex]
      rw [← Finset.sum_mul]
      unfold unitMean
      ring

theorem affineAverage_centered {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) (t : ZMod p) :
    affineAverage W (fieldCentered F) t =
      affineAverage W F t - unitMean W * fieldMean F := by
  simp only [affineAverage, fieldCentered, unitMean, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  ring

theorem affineAverage_centered_function {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (F : ZMod p → ℂ) :
    affineAverage W (fieldCentered F) = fieldCentered (affineAverage W F) := by
  funext t
  rw [affineAverage_centered, fieldCentered, affineAverage_mean]

theorem affineAverage_full_energy_bound {p : ℕ} [Fact p.Prime]
    (W : (ZMod p)ˣ → ℂ) (hW : (∑ r : (ZMod p)ˣ, ‖W r‖ ^ 2) ≤ (p : ℝ))
    (F : ZMod p → ℂ) :
    (∑ t : ZMod p, ‖affineAverage W F t‖ ^ 2) ≤
      Real.sqrt (3 / (p : ℝ)) * (∑ t : ZMod p, ‖F t‖ ^ 2) +
        (p : ℝ) * ‖unitMean W‖ ^ 2 * ‖fieldMean F‖ ^ 2 := by
  rw [fieldCentered_energy_identity (affineAverage W F), affineAverage_mean,
    ← affineAverage_centered_function, norm_mul, mul_pow]
  have hcenter := (affineAverage_energy_bound W hW (fieldCentered F)
    (fieldCentered_fourier_zero F)).trans
      (mul_le_mul_of_nonneg_left (fieldCentered_energy_le F) (Real.sqrt_nonneg _))
  nlinarith

theorem unitMean_conj_of_zero {p : ℕ} [Fact p.Prime]
    (G : ZMod p → ℂ) (hG : G 0 = 0) :
    unitMean (fun r : (ZMod p)ˣ => conj (G r)) = conj (fieldMean G) := by
  unfold unitMean
  rw [sum_units_eq_sum_of_zero (fun x : ZMod p => conj (G x)) (by simp only [hG, map_zero]),
    fieldMean_eq_sum]
  simp only [map_mul, map_inv₀, map_natCast, map_sum]

/-- The exact affine self-correlation estimate underlying `src42`. -/
theorem affineAverage_self_correlation_bound {p : ℕ} [Fact p.Prime]
    (G : ZMod p → ℂ) (hG0 : G 0 = 0)
    (hG : (∑ t : ZMod p, ‖G t‖ ^ 2) ≤ (p : ℝ)) :
    (∑ t : ZMod p, ‖affineAverage (fun r : (ZMod p)ˣ => conj (G r)) G t‖ ^ 2) /
      (p : ℝ) ≤ ‖fieldMean G‖ ^ 4 + Real.sqrt (3 / (p : ℝ)) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hW : (∑ r : (ZMod p)ˣ, ‖conj (G r)‖ ^ 2) ≤ (p : ℝ) := by
    simp_rw [Complex.norm_conj]
    rw [sum_units_eq_sum_of_zero (fun t : ZMod p => ‖G t‖ ^ 2) (by simp [hG0])]
    exact hG
  have h := affineAverage_full_energy_bound (fun r : (ZMod p)ˣ => conj (G r)) hW G
  rw [unitMean_conj_of_zero G hG0, Complex.norm_conj] at h
  apply (div_le_iff₀ hp).mpr
  have hs := mul_le_mul_of_nonneg_left hG (Real.sqrt_nonneg (3 / (p : ℝ)))
  nlinarith

/-- Restricting the output to units costs only the factor `p/(p-1)`. -/
theorem affineAverage_self_correlation_unit_bound {p : ℕ} [Fact p.Prime]
    (G : ZMod p → ℂ) (hG0 : G 0 = 0)
    (hG : (∑ t : ZMod p, ‖G t‖ ^ 2) ≤ (p : ℝ)) :
    (∑ t : (ZMod p)ˣ, ‖affineAverage (fun r : (ZMod p)ˣ => conj (G r)) G t‖ ^ 2) /
      ((p : ℝ) - 1) ≤ ((p : ℝ) / ((p : ℝ) - 1)) *
        (‖fieldMean G‖ ^ 4 + Real.sqrt (3 / (p : ℝ))) := by
  classical
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : 0 < (p : ℝ) - 1 := by
    have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  have hsub : (∑ t : (ZMod p)ˣ,
      ‖affineAverage (fun r : (ZMod p)ˣ => conj (G r)) G t‖ ^ 2) ≤
      ∑ t : ZMod p, ‖affineAverage (fun r : (ZMod p)ˣ => conj (G r)) G t‖ ^ 2 :=
    Finset.sum_le_sum_of_injOn (fun t : (ZMod p)ˣ => (t : ZMod p))
      Units.val_injective.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
      (fun _ _ _ => sq_nonneg _)
  calc
    _ ≤ (∑ t : ZMod p, ‖affineAverage (fun r : (ZMod p)ˣ => conj (G r)) G t‖ ^ 2) /
        ((p : ℝ) - 1) := div_le_div_of_nonneg_right hsub hp1.le
    _ = ((p : ℝ) / ((p : ℝ) - 1)) *
        ((∑ t : ZMod p, ‖affineAverage (fun r : (ZMod p)ˣ => conj (G r)) G t‖ ^ 2) /
          (p : ℝ)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (affineAverage_self_correlation_bound G hG0 hG) (div_nonneg hp.le hp1.le)

end Ostmann

end OAI
