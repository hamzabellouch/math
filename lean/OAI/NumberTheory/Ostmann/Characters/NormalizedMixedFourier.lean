import OAI.NumberTheory.Ostmann.Characters.NormalizedResidueIndicator
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityFourierBounds
import OAI.NumberTheory.Ostmann.Characters.GaussFourier

namespace OAI

/-! # Mixed Fourier coefficients of the normalized residue transform

The principal coefficient is controlled by Fourier inversion. Nonprincipal
coefficients are exactly the translated residue bias times its density factor.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem additiveFourier_densityFourier {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (densityFourier f) a =
      (Real.sqrt (p : ℝ) : ℂ) * (p : ℂ)⁻¹ * f (-a) := by
  change additiveFourier (fun x => (Real.sqrt (p : ℝ) : ℂ) * additiveFourier f x) a = _
  rw [additiveFourier_const_mul, additiveFourier_twice]
  ring

theorem normalizedResidueTransform_principal {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (a : ZMod p) :
    ‖additiveFourier (fun x => normalizedResidueTransform S x * (1 : MulChar (ZMod p) ℂ) x) a‖ =
      ‖normalizedResidueIndicator S (-a)‖ / Real.sqrt (p : ℝ) := by
  have he : (fun x => normalizedResidueTransform S x * (1 : MulChar (ZMod p) ℂ) x) =
      normalizedResidueTransform S := by
    funext x
    by_cases hx : x = 0
    · simp [hx, normalizedResidueTransform_zero]
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hx), mul_one]
  rw [he, normalizedResidueTransform, additiveFourier_densityFourier,
    norm_mul, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp
  have hs2 := Real.sq_sqrt hp.le
  field_simp
  rw [hs2]

theorem densityFourier_mixed_character {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    additiveFourier (fun x => densityFourier f x * χ x) a =
      ((Real.sqrt (p : ℝ) : ℂ) * (p : ℂ)⁻¹ ^ 2 * gaussSum χ ZMod.stdAddChar) *
        ∑ x : ZMod p, f x * χ⁻¹ (-a - x) := by
  rw [additiveFourier_mul_character _ χ hχ]
  simp_rw [additiveFourier_densityFourier]
  have he : (∑ b : ZMod p, f (-b) * χ⁻¹ (-(a - b))) =
      ∑ x : ZMod p, f x * χ⁻¹ (-a - x) := by
    have hh := (Equiv.neg (ZMod p)).bijective.sum_comp (fun x => f x * χ⁻¹ (-a - x))
    simpa only [Equiv.neg_apply, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm] using hh
  calc
    _ = ((Real.sqrt (p : ℝ) : ℂ) * (p : ℂ)⁻¹ ^ 2 * gaussSum χ ZMod.stdAddChar) *
        ∑ b : ZMod p, f (-b) * χ⁻¹ (-(a - b)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [he]

theorem normalizedResidueIndicator_character_sum {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    (∑ x : ZMod p, normalizedResidueIndicator S x * χ⁻¹ (-a - x)) =
      (Real.sqrt (residueVariance S) : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x) := by
  have hsum : (∑ x : ZMod p, χ⁻¹ (-a - x)) = 0 := by
    have hh := (Equiv.subLeft (-a)).bijective.sum_comp (fun x => χ⁻¹ x)
    change (∑ x : ZMod p, χ⁻¹ (-a - x)) = ∑ x : ZMod p, χ⁻¹ x at hh
    rw [hh]
    exact MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hχ)
  have hf (x : ZMod p) : normalizedResidueIndicator S x =
      (Real.sqrt (residueVariance S) : ℂ)⁻¹ *
        ((if x ∈ S then 1 else 0) - (residueDensity S : ℂ)) := by
    simp only [normalizedResidueIndicator, centeredDensity, residueDensity,
      Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_natCast]
    split <;> push_cast <;> ring
  simp_rw [hf, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero]
  simp

theorem normalizedResidueTransform_nonprincipal {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p)
    (hS : S.Nonempty) (hSp : S.card < p) :
    ‖additiveFourier (fun x => normalizedResidueTransform S x * χ x) a‖ =
      residueDensity S / Real.sqrt (residueVariance S) *
        ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ := by
  rw [normalizedResidueTransform, densityFourier_mixed_character _ χ hχ,
    normalizedResidueIndicator_character_sum S χ hχ a]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hv := residueVariance_pos S hS hSp
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp
  have hsv : 0 < Real.sqrt (residueVariance S) := Real.sqrt_pos.mpr hv
  have hgauss : ‖gaussSum χ (ZMod.stdAddChar (N := p))‖ = Real.sqrt (p : ℝ) := by
    have hh := gaussSum_norm_sq χ hχ
    have he := Real.sq_sqrt hp.le
    nlinarith [norm_nonneg (gaussSum χ (ZMod.stdAddChar (N := p))), Real.sqrt_nonneg (p : ℝ)]
  simp only [norm_mul, norm_pow, norm_inv, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs, abs_of_pos hsv, hgauss, residueDensity]
  have hs2 := Real.sq_sqrt hp.le
  field_simp
  rw [hs2]

/-- The exact Gauss identity supplies the local mixed bound used by the tree
comparison once the translated character means have been bounded. -/
theorem normalizedResidueTransform_mixedBound {p : ℕ} [Fact p.Prime]
    (S : Finset (ZMod p)) (hlo : (1 / 3 : ℝ) ≤ residueDensity S)
    (hhi : residueDensity S ≤ 2 / 3) (β : ℝ)
    (hbias : ∀ (χ : MulChar (ZMod p) ℂ), χ ≠ 1 → ∀ a : ZMod p,
      ‖(S.card : ℂ)⁻¹ * ∑ x ∈ S, χ⁻¹ (-a - x)‖ ≤ β) :
    MixedFourierBound (normalizedResidueTransform S)
      (max (3 / Real.sqrt (p : ℝ)) (2 * β)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < S.card := by
      have hh : 0 < residueDensity S := by linarith
      exact (div_pos_iff_of_pos_right hp).mp hh
    exact_mod_cast hpos
  have hSp : S.card < p := by
    have hh : residueDensity S < 1 := by linarith
    exact_mod_cast (div_lt_one hp).mp hh
  have hv : (1 / 9 : ℝ) ≤ residueVariance S := by
    dsimp [residueVariance]
    nlinarith
  have hs : (1 / 3 : ℝ) ≤ Real.sqrt (residueVariance S) := by
    have hh := Real.sq_sqrt (show 0 ≤ residueVariance S by linarith)
    nlinarith [Real.sqrt_nonneg (residueVariance S)]
  have hsv : 0 < Real.sqrt (residueVariance S) := by linarith
  have hratio : residueDensity S / Real.sqrt (residueVariance S) ≤ 2 :=
    (div_le_iff₀ hsv).mpr (by linarith)
  intro χ a
  by_cases hχ : χ = 1
  · subst χ
    rw [normalizedResidueTransform_principal]
    exact (div_le_div_of_nonneg_right (normalizedResidueIndicator_norm_le_three S hlo hhi (-a))
      (Real.sqrt_nonneg _)).trans (le_max_left _ _)
  · rw [normalizedResidueTransform_nonprincipal S χ hχ a hS hSp]
    exact (mul_le_mul hratio (hbias χ hχ a) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).trans
      (le_max_right _ _)

end Ostmann

end OAI
