import OAI.NumberTheory.Ostmann.Characters.ConjugatedPairMeans
import OAI.NumberTheory.Ostmann.Characters.QuartetSpectrumBound

namespace OAI

/-! # Concrete Fourier mass bounds needed in the cross-pair application -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance pairFourierMassFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem norm_characterTwist_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (x : ZMod p) :
    ‖characterTwist g χ x‖ ≤ ‖g x‖ := by
  by_cases hx : x = 0
  · simp [hx, characterTwist, MulChar.map_zero]
  · have hn := norm_mulChar_unit χ (Units.mk0 x hx)
    simp only [characterTwist, norm_mul, Complex.norm_conj, Units.val_mk0] at hn ⊢
    rw [hn, mul_one]

theorem characterTwist_energy_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) :
    (∑ x : ZMod p, ‖characterTwist g χ x‖ ^ 2) ≤ ∑ x : ZMod p, ‖g x‖ ^ 2 := by
  exact Finset.sum_le_sum fun x _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_characterTwist_le g χ x) 2

theorem pairAutocorrelation_fourier_formula {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    additiveFourier (pairAutocorrelation g χ) a =
      (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) *
        ‖additiveFourier (characterTwist g χ) a‖ ^ 2 : ℝ) : ℂ) := by
  change additiveFourier (fun d => (p : ℂ) / (Fintype.card (ZMod p)ˣ : ℂ) *
    additiveAutocorrelation (characterTwist g χ) d) a = _
  rw [additiveFourier_const_mul, additiveFourier_autocorrelation]
  push_cast
  rfl

theorem pairAutocorrelation_weight_mass_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ a : ZMod p, (p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) *
      ‖additiveFourier (characterTwist g χ) a‖ ^ 2) ≤
        (p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) := by
  rw [← Finset.mul_sum, additiveFourier_parseval]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h := (characterTwist_energy_le g χ).trans henergy
  calc
    _ ≤ (p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) * ((p : ℝ)⁻¹ * p) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by positivity)) (by positivity)
    _ = _ := by rw [inv_mul_cancel₀ hp, mul_one]

theorem pairAutocorrelation_zero_norm_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    ‖pairAutocorrelation g χ 0‖ ≤ (p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ) := by
  exact (norm_at_zero_le_spectrum_mass _ _ (pairAutocorrelation_fourier_formula g χ)
    (fun _ => by positivity)).trans (pairAutocorrelation_weight_mass_le g χ henergy)

theorem fieldPairCoefficientMoment_eq_pairAutocorrelation {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (d : ZMod p) (hd : d ≠ 0) :
    fieldPairCoefficientMoment g χ d = ‖pairAutocorrelation g χ d‖ ^ 2 := by
  let du : (ZMod p)ˣ := Units.mk0 d hd
  have he : (fun t : (ZMod p)ˣ => fieldBottomPairValue g d t) = bottomPairValue g du := by
    funext t
    simp only [fieldBottomPairValue, hd, Units.ne_zero, dite_false, Units.mk0_val, du]
  unfold fieldPairCoefficientMoment
  rw [he, bottomPair_mellin_autocorrelation]
  rfl

theorem pairAutocorrelation_point_energy_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) (d : ZMod p) :
    ‖pairAutocorrelation g χ d‖ ^ 2 ≤ fieldPairCoefficientMoment g χ d +
      if d = 0 then ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 else 0 := by
  by_cases hd : d = 0
  · simp only [hd, fieldPairCoefficientMoment_zero, ite_true, zero_add]
    exact pow_le_pow_left₀ (norm_nonneg _) (pairAutocorrelation_zero_norm_le g χ henergy) 2
  · rw [fieldPairCoefficientMoment_eq_pairAutocorrelation g χ d hd, ite_eq_right hd, add_zero]

theorem pairAutocorrelation_fourier_energy_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hflat : MixedFourierBound g ε)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ a : ZMod p, ‖additiveFourier (pairAutocorrelation g χ) a‖ ^ 2) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 * ε ^ 2 := by
  have hauto := autocorrelation_energy_le_fourier_sup (characterTwist g χ) ε hε
    (hflat.characterTwist χ)
  have he := (characterTwist_energy_le g χ).trans henergy
  rw [additiveFourier_parseval]
  have hP (d : ZMod p) : ‖pairAutocorrelation g χ d‖ ^ 2 =
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        ‖additiveAutocorrelation (characterTwist g χ) d‖ ^ 2 := by
    simp only [pairAutocorrelation, norm_mul, norm_div, Complex.norm_natCast, mul_pow]
  simp_rw [hP]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (p : ℝ)⁻¹ * (((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 * (ε ^ 2 * p)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (hauto.trans (mul_le_mul_of_nonneg_left he (sq_nonneg _))) (sq_nonneg _)
    _ = _ := by
      have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      field_simp

theorem pairAutocorrelation_total_point_energy_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ d : ZMod p, ‖pairAutocorrelation g χ d‖ ^ 2) ≤
      2 * (Fintype.card (ZMod p)ˣ : ℝ) *
        ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (MulChar (ZMod p) ℂ)))
    (fun χ _ => Finset.sum_le_sum (s := (Finset.univ : Finset (ZMod p)))
      (fun d _ => pairAutocorrelation_point_energy_le g χ henergy d))
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_mulChar_eq_card_units] at h
  have hF : (∑ χ : MulChar (ZMod p) ℂ, ∑ d : ZMod p, fieldPairCoefficientMoment g χ d) =
      ∑ d : ZMod p, fieldPairMoment g d := by
    rw [Finset.sum_comm]
    simp_rw [sum_fieldPairCoefficientMoment]
  rw [hF] at h
  have hU : 0 < (Fintype.card (ZMod p)ˣ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hR := (div_le_iff₀ hU).mp (fieldPairMoment_mean_le g hg henergy)
  nlinarith

theorem pairAutocorrelation_total_fourier_energy_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖additiveFourier (pairAutocorrelation g χ) a‖ ^ 2) ≤
      2 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) := by
  simp_rw [additiveFourier_parseval]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left (pairAutocorrelation_total_point_energy_le g hg henergy)
    (show 0 ≤ (p : ℝ)⁻¹ by positivity)).trans_eq
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

end Ostmann

end OAI
