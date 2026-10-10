import OAI.NumberTheory.Ostmann.Preliminaries.TwoBadFourier

namespace OAI

/-!
# The two-bad quartet estimate in terms of its spectra

The hypotheses are the nonnegative spectrum bounds `src40`. This combines
the previously proved Gauss fourth moment with all principal corrections.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetSpectrumFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance quartetSpectrumDecidableEq {p : ℕ} :
    DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

theorem norm_at_zero_le_spectrum_mass {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ a, additiveFourier f a = (w a : ℂ)) (hw : ∀ a, 0 ≤ w a) :
    ‖f 0‖ ≤ ∑ a : ZMod p, w a := by
  rw [additiveFourier_inversion f 0]
  simp only [mul_zero, AddChar.map_zero_eq_one, mul_one, hf]
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _)] using
    norm_sum_le (Finset.univ : Finset (ZMod p)) (fun a => (w a : ℂ))

theorem principal_fourier_norm_sq_le {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ a, additiveFourier f a = (w a : ℂ)) (hw : ∀ a, 0 ≤ w a)
    (J W : ℝ) (hmass : (∑ a : ZMod p, w a) ≤ J) (hmax : ∀ a, w a ≤ W)
    (a : ZMod p) :
    ‖additiveFourier (fun x => f x * (1 : MulChar (ZMod p) ℂ) x) a‖ ^ 2 ≤
      (W + (p : ℝ)⁻¹ * J) ^ 2 := by
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [additiveFourier_principal_twist, hf]
  calc
    _ ≤ ‖(w a : ℂ)‖ + ‖(p : ℂ)⁻¹ * f 0‖ := norm_sub_le _ _
    _ = w a + (p : ℝ)⁻¹ * ‖f 0‖ := by
      simp only [norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (hw a)]
    _ ≤ W + (p : ℝ)⁻¹ * J := add_le_add (hmax a)
      (mul_le_mul_of_nonneg_left ((norm_at_zero_le_spectrum_mass f w hf hw).trans hmass)
        (inv_nonneg.mpr (Nat.cast_nonneg p)))

theorem character_spectrum_energy_le {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (w : ZMod p → ℝ)
    (hf : ∀ a, additiveFourier f a = (w a : ℂ))
    (α : MulChar (ZMod p) ℂ) :
    (∑ a : ZMod p, ‖additiveFourier (fun x => f x * α x) a‖ ^ 2) ≤
      ∑ a : ZMod p, w a ^ 2 := by
  have h := additiveFourier_character_energy_le f α
  simpa only [hf, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

/-- Complete bound for the two-bad row of `tree-twisted-convolution`. -/
theorem two_bad_spectrum_sum_le {p : ℕ} [Fact p.Prime]
    (f g : MulChar (ZMod p) ℂ → ZMod p → ℂ)
    (w v : MulChar (ZMod p) ℂ → ZMod p → ℝ)
    (hf : ∀ χ a, additiveFourier (f χ) a = (w χ a : ℂ))
    (hg : ∀ χ a, additiveFourier (g χ) a = (v χ a : ℂ))
    (hw : ∀ χ a, 0 ≤ w χ a) (hv : ∀ χ a, 0 ≤ v χ a)
    (J W R S : ℝ) (hR : 0 ≤ R)
    (hwmass : ∀ χ, (∑ a : ZMod p, w χ a) ≤ J)
    (hvmass : ∀ χ, (∑ a : ZMod p, v χ a) ≤ J)
    (hwmax : ∀ χ a, w χ a ≤ W)
    (hwr : ∀ χ, (∑ a : ZMod p, w χ a ^ 2) ≤ R)
    (hvr : ∀ χ, (∑ a : ZMod p, v χ a ^ 2) ≤ R)
    (hws : (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, w χ a ^ 2) ≤ S)
    (hvs : (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, v χ a ^ 2) ≤ S)
    (ν : MulChar (ZMod p) ℂ) :
    (∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
      ‖additiveFourier (fun x => f χ x * (ν * ψ⁻¹) x) a‖ ^ 2 *
        ‖additiveFourier (fun x => g ψ x * (ν⁻¹ * χ⁻¹) x) (-a)‖ ^ 2) ≤
      (2 * ((Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ)) * R * S +
        3 * ((Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ) ^ 2) * J ^ 4) +
      2 * ((p : ℝ)⁻¹ * J ^ 2) * S + (W + (p : ℝ)⁻¹ * J) ^ 2 * R := by
  have hS : 0 ≤ S := (by positivity :
    0 ≤ ∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, w χ a ^ 2).trans hws
  apply two_bad_fourier_sum_le
    (fun χ α a => additiveFourier (fun x => f χ x * α x) a)
    (fun ψ β a => additiveFourier (fun x => g ψ x * β x) a) ν
  · positivity
  · positivity
  · positivity
  · exact nonprincipal_fourth_family_bound f w hf hw J R S hR hwmass hwr hws
  · exact nonprincipal_fourth_family_bound g v hg hv J R S hR hvmass hvr hvs
  · intro χ α hα a
    exact nonprincipal_fourier_norm_sq_le (f χ) (w χ) (hf χ) (hw χ) J (hwmass χ) α hα a
  · intro ψ β hβ a
    exact nonprincipal_fourier_norm_sq_le (g ψ) (v ψ) (hg ψ) (hv ψ) J (hvmass ψ) β hβ a
  · intro χ a
    exact principal_fourier_norm_sq_le (f χ) (w χ) (hf χ) (hw χ) J W (hwmass χ) (hwmax χ) a
  · exact (Finset.sum_le_sum fun χ _ => character_spectrum_energy_le (f χ) (w χ) (hf χ) 1).trans hws
  · exact (Finset.sum_le_sum fun ψ _ => character_spectrum_energy_le (g ψ) (v ψ) (hg ψ) 1).trans hvs
  · intro ψ
    exact (character_spectrum_energy_le (g ψ) (v ψ) (hg ψ) 1).trans (hvr ψ)

end Ostmann

end OAI
