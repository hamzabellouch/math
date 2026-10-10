import OAI.NumberTheory.Ostmann.Supply.ResidueProjectionScalar
import OAI.NumberTheory.Ostmann.Supply.CenteredResidueProjection

namespace OAI

/-! # Quantitative side blocks of the sparse residue projection -/

namespace Ostmann
open scoped Classical BigOperators

theorem centered_spectral_affine_energy {p : ℕ} [NeZero p]
    (E T : Finset (ZMod p)) (hE : 0 ∉ E) (f : ZMod p → ℂ) (a c : ℂ) :
    (∑ x, ‖centeredSupportProjection T
      (finiteSpectralProjection E (fun x => a * f x + c)) x‖ ^ 2) =
      ‖a‖ ^ 2 * ∑ x, ‖centeredSupportProjection T (finiteSpectralProjection E f) x‖ ^ 2 := by
  rw [finiteSpectralProjection_affine E hE, centeredSupportProjection_const_mul]
  simp only [norm_mul, mul_pow, Finset.mul_sum]

theorem residue_uniform_coefficient_sq {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) :
    (Real.sqrt (residueVariance S) / S.card) ^ 2 ≤ 2 / (p : ℝ) ^ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hs : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hps : (p : ℝ) ≤ 3 * S.card := by
    rw [residueDensity, le_div_iff₀ hp] at hlo
    linarith
  have hv : residueVariance S = (S.card : ℝ) * (p - S.card) / (p : ℝ) ^ 2 := by
    unfold residueVariance residueDensity
    field_simp
  rw [div_pow, Real.sq_sqrt (residueVariance_pos S hS hSp).le, hv]
  apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hp)).mpr
  nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hps)]

theorem residue_compl_coefficient_sq {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p)
    (hhi : residueDensity S ≤ 2 / 3) :
    (-Real.sqrt (residueVariance S) / ((p : ℝ) - S.card)) ^ 2 ≤ 2 / (p : ℝ) ^ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hs : (0 : ℝ) < (p : ℝ) - S.card := sub_pos.mpr (by exact_mod_cast hSp)
  have hps : 3 * (S.card : ℝ) ≤ 2 * p := by
    rw [residueDensity, div_le_iff₀ hp] at hhi
    linarith
  have hv : residueVariance S = (S.card : ℝ) * (p - S.card) / (p : ℝ) ^ 2 := by
    unfold residueVariance residueDensity
    field_simp
  rw [div_pow, neg_sq, Real.sq_sqrt (residueVariance_pos S hS hSp).le, hv]
  apply (div_le_iff₀ (sq_pos_of_pos hs)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hp)).mpr
  nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hps)]

/-- Either uniform-support side of the projection is O(epsilon/sqrt(p)),
in the squared-energy form used to bound the local block matrix. -/
theorem residueProjection_side_energy {p : ℕ} [NeZero p]
    (S E : Finset (ZMod p)) (hS : S.Nonempty) (hSp : S.card < p) (hE : 0 ∉ E)
    (hlo : (1 / 3 : ℝ) ≤ residueDensity S) (hhi : residueDensity S ≤ 2 / 3)
    (ε : ℝ)
    (herr : (∑ x, ‖normalizedResidueIndicator S x -
      finiteSpectralProjection E (normalizedResidueIndicator S) x‖ ^ 2) ≤ ε ^ 2 * p) :
    (∑ x, ‖centeredSupportProjection (Finset.univ \ S)
      (finiteSpectralProjection E (uniformResidueVector S)) x‖ ^ 2) ≤ 2 * ε ^ 2 / p ∧
    (∑ x, ‖centeredSupportProjection S
      (finiteSpectralProjection E (uniformResidueVector (Finset.univ \ S))) x‖ ^ 2) ≤ 2 * ε ^ 2 / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hbound (T : Finset (ZMod p)) (a c : ℝ)
      (hT : centeredSupportProjection T (normalizedResidueIndicator S) = fun _ => 0)
      (ha : a ^ 2 ≤ 2 / (p : ℝ) ^ 2) :
      (∑ x, ‖centeredSupportProjection T (finiteSpectralProjection E
        (fun x => (a : ℂ) * normalizedResidueIndicator S x + (c : ℂ))) x‖ ^ 2) ≤
          2 * ε ^ 2 / p := by
    rw [centered_spectral_affine_energy E T hE]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    calc
      _ ≤ a ^ 2 * (ε ^ 2 * p) := mul_le_mul_of_nonneg_left
        (centered_residue_projection_energy_le S E T ε hT herr) (sq_nonneg _)
      _ ≤ (2 / (p : ℝ) ^ 2) * (ε ^ 2 * p) :=
        mul_le_mul_of_nonneg_right ha (mul_nonneg (sq_nonneg _) hp.le)
      _ = _ := by field_simp
  constructor
  · have he := funext (uniformResidueVector_affine S hS hSp)
    rw [he]
    exact hbound _ _ _ (centeredSupportProjection_compl_residue_zero S)
      (residue_uniform_coefficient_sq S hS hSp hlo)
  · have he := funext (uniformResidueVector_compl_affine S hS hSp)
    rw [he]
    exact hbound _ _ _ (centeredSupportProjection_residue_zero S)
      (residue_compl_coefficient_sq S hS hSp hhi)

end Ostmann

end OAI
