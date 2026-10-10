import OAI.NumberTheory.DirichletL.Hecke.IdealBridge
import OAI.NumberTheory.DirichletL.IdealEuler

namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

private instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem idealCoeff_norm_le_one (χ : Character) (I : Ideal O) : ‖idealCoeff χ I‖ ≤ 1 := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact IdealCharacter.norm_ofResidue_le_one χ.modulus χ.residue χ.unit_trivial I

theorem idealTerm_eq_weighted (χ : Character) (s : ℂ) (I : Ideal O) :
    idealTerm χ s I = IdealEuler.weighted (idealCoeff χ) s I := by
  change idealCoeff χ I / (Ideal.absNorm I : ℂ)^s =
    idealCoeff χ I * CubicEisenstein.fullIdealWeight s I
  by_cases hI : I = 0
  · rw [hI, map_zero]
    simp
  · simp only [CubicEisenstein.fullIdealWeight, hI, ite_false,
      Complex.cpow_neg, div_eq_mul_inv]

theorem LFunction_eq_series (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = IdealEuler.series (idealCoeff χ) s := by
  rw [LFunction_eq_ideal_tsum χ hs]
  exact tsum_congr (idealTerm_eq_weighted χ s)

theorem LFunction_ne_zero_of_one_lt_re (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s ≠ 0 := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.series_ne_zero (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs

theorem inverseSeries_mul_LFunction (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    IdealEuler.inverseSeries (idealCoeff χ) s * LFunction χ s = 1 := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.inverseSeries_mul_series (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs

theorem LFunction_eq_normFiber_LSeries (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = LSeries (ShortDraftHeckeBridge.normFiberCoeff (idealCoeff χ)) s := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.series_eq_LSeries (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs

end SevenEighths.HeckeFamily

end

end OAI
