import OAI.NumberTheory.Ostmann.Tree.PairFourierMass

namespace OAI

/-! # The quartet Fourier estimate with the actual autocorrelation spectra -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance concreteQuartetFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def twoBadQuartetError (p : ℕ) [Fact p.Prime] (ε : ℝ) : ℝ :=
  let U : ℝ := Fintype.card (ZMod p)ˣ
  let C : ℝ := p / U
  (2 * (U / p) * (C ^ 2 * ε ^ 2) * (2 * C) + 3 * (U / (p : ℝ) ^ 2) * C ^ 4) +
    2 * ((p : ℝ)⁻¹ * C ^ 2) * (2 * C) +
      (C * ε ^ 2 + (p : ℝ)⁻¹ * C) ^ 2 * (C ^ 2 * ε ^ 2)

theorem twoBadQuartetError_nonneg (p : ℕ) [Fact p.Prime] (ε : ℝ) :
    0 ≤ twoBadQuartetError p ε := by unfold twoBadQuartetError; positivity

theorem concrete_two_bad_fourier_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (hg : g 0 = 0) (hh : h 0 = 0)
    (heg : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (heh : (∑ x : ZMod p, ‖h x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hfg : MixedFourierBound g ε) (hfh : MixedFourierBound h ε)
    (ν : MulChar (ZMod p) ℂ) :
    quartetFourierEnergy (pairAutocorrelation g) (pairAutocorrelation h) false false ν ≤
      twoBadQuartetError p ε := by
  let U : ℝ := Fintype.card (ZMod p)ˣ
  let C : ℝ := p / U
  let w (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) : ℝ :=
    C * ‖additiveFourier (characterTwist f χ) a‖ ^ 2
  have hweight (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
      additiveFourier (pairAutocorrelation f χ) a = (w f χ a : ℂ) :=
    pairAutocorrelation_fourier_formula f χ a
  have hn (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (a : ZMod p) : 0 ≤ w f χ a := by
    dsimp [w, C, U]
    positivity
  have hmass (f : ZMod p → ℂ) (he : (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ (p : ℝ))
      (χ : MulChar (ZMod p) ℂ) : (∑ a : ZMod p, w f χ a) ≤ C :=
    pairAutocorrelation_weight_mass_le f χ he
  have hmax (χ : MulChar (ZMod p) ℂ) (a : ZMod p) : w g χ a ≤ C * ε ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by dsimp [C, U]; positivity)
    exact (sq_le_sq₀ (norm_nonneg _) hε).mpr (hfg.characterTwist χ a)
  have hrow (f : ZMod p → ℂ) (he : (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ (p : ℝ))
      (hf : MixedFourierBound f ε) (χ : MulChar (ZMod p) ℂ) :
      (∑ a : ZMod p, w f χ a ^ 2) ≤ C ^ 2 * ε ^ 2 := by
    have hb := pairAutocorrelation_fourier_energy_le f χ ε hε hf he
    simpa only [hweight, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hb
  have htotal (f : ZMod p → ℂ) (hf : f 0 = 0)
      (he : (∑ x : ZMod p, ‖f x‖ ^ 2) ≤ (p : ℝ)) :
      (∑ χ : MulChar (ZMod p) ℂ, ∑ a : ZMod p, w f χ a ^ 2) ≤ 2 * C := by
    have hb := pairAutocorrelation_total_fourier_energy_le f hf he
    simpa only [hweight, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hb
  have hb := two_bad_spectrum_sum_le (pairAutocorrelation g) (pairAutocorrelation h)
    (w g) (w h) (hweight g) (hweight h) (hn g) (hn h)
    C (C * ε ^ 2) (C ^ 2 * ε ^ 2) (2 * C) (by positivity)
    (hmass g heg) (hmass h heh) hmax (hrow g heg hfg) (hrow h heh hfh)
    (htotal g hg heg) (htotal h hh heh) ν
  simpa only [quartetFourierEnergy, quartetLeftTwist, quartetRightTwist,
    Bool.false_eq_true, ite_false, mul_one, twoBadQuartetError] using hb

noncomputable def friendlyQuartetError (p : ℕ) [Fact p.Prime] (ε : ℝ) : ℝ :=
  2 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
    (ε ^ 4 + Real.sqrt (3 / (p : ℝ)))

theorem friendlyQuartetError_nonneg (p : ℕ) [Fact p.Prime] (ε : ℝ) :
    0 ≤ friendlyQuartetError p ε := by unfold friendlyQuartetError; positivity

theorem concrete_left_friendly_fourier_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (hg : g 0 = 0) (hh : h 0 = 0)
    (heg : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (heh : (∑ x : ZMod p, ‖h x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hfg : MixedFourierBound g ε) (right : Bool) (ν : MulChar (ZMod p) ℂ) :
    quartetFourierEnergy (pairAutocorrelation g) (pairAutocorrelation h) true right ν ≤
      friendlyQuartetError p ε := by
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : p.Prime).one_lt.le, Nat.cast_one]
  have hb := left_friendly_fourier_sum_le (pairAutocorrelation g) (pairAutocorrelation h)
    (((p : ℝ) / ((p : ℝ) - 1)) * (ε ^ 4 + Real.sqrt (3 / (p : ℝ))))
    (2 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)))
    (by rw [← hU]; positivity)
    (fun η a => uniform_mellin_bound_of_fourier_bound g hg heg ε hfg η a)
    (pairAutocorrelation_total_fourier_energy_le h hh heh) right ν
  apply hb.trans_eq
  dsimp [friendlyQuartetError]
  rw [hU]
  ring

theorem concrete_quartet_fourier_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (hg : g 0 = 0) (hh : h 0 = 0)
    (heg : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (heh : (∑ x : ZMod p, ‖h x‖ ^ 2) ≤ (p : ℝ))
    (ε : ℝ) (hε : 0 ≤ ε) (hfg : MixedFourierBound g ε) (hfh : MixedFourierBound h ε)
    (left right : Bool) (ν : MulChar (ZMod p) ℂ) :
    quartetFourierEnergy (pairAutocorrelation g) (pairAutocorrelation h) left right ν ≤
      friendlyQuartetError p ε + twoBadQuartetError p ε := by
  cases left
  · cases right
    · exact (concrete_two_bad_fourier_le g h hg hh heg heh ε hε hfg hfh ν).trans
        (le_add_of_nonneg_left (friendlyQuartetError_nonneg p ε))
    · rw [quartetFourierEnergy_swap]
      exact (concrete_left_friendly_fourier_le h g hh hg heh heg ε hfh false ν⁻¹).trans
        (le_add_of_nonneg_right (twoBadQuartetError_nonneg p ε))
  · exact (concrete_left_friendly_fourier_le g h hg hh heg heh ε hfg right ν).trans
      (le_add_of_nonneg_right (twoBadQuartetError_nonneg p ε))

end Ostmann

end OAI
