import OAI.NumberTheory.DirichletL.Hecke.DyadicMellin
import OAI.NumberTheory.DirichletL.Hecke.LogDerivative

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

private instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
private instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def coefficient (χ : Character) (I : Ideal O) : ℂ :=
  (IdealMangoldt.value I : ℂ) * idealCoeff χ I

@[simp] theorem coefficient_zero (χ : Character) : coefficient χ 0 = 0 := by
  unfold coefficient
  rw [IdealMangoldt.value_zero, Complex.ofReal_zero, zero_mul]

def series (χ : Character) (s : ℂ) : ℂ := -deriv (LFunction χ) s / LFunction χ s

theorem series_eq_tsum (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    series χ s = ∑' I : NonzeroIdeal, coefficient χ I.val * (norm I : ℂ)^(-s) := by
  have he : (∑' I : NonzeroIdeal, (IdealMangoldt.value I.val : ℂ) *
      IdealEuler.weighted (idealCoeff χ) s I.val) =
      ∑' I : Ideal O, (IdealMangoldt.value I : ℂ) * IdealEuler.weighted (idealCoeff χ) s I := by
    apply tsum_subtype_eq_of_support_subset (s := {I : Ideal O | I ≠ 0})
      (f := fun I : Ideal O => (IdealMangoldt.value I : ℂ) * IdealEuler.weighted (idealCoeff χ) s I)
    intro I hI hi
    subst I
    exact hI (by
      change (IdealMangoldt.value 0 : ℂ) * IdealEuler.weighted (idealCoeff χ) s 0 = 0
      rw [IdealMangoldt.value_zero, Complex.ofReal_zero, zero_mul])
  change -deriv (LFunction χ) s / LFunction χ s = _
  rw [← HeckeLogDerivative.coeff_LSeries_eq χ hs]
  change LSeries (IdealLogDerivative.coeff (idealCoeff χ)) s = _
  rw [← IdealLogDerivative.mangoldt_series_eq_LSeries _ (idealCoeff_norm_le_one χ) s hs, ← he]
  apply tsum_congr
  intro I
  simp only [coefficient, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight]
  rw [ite_eq_right_iff.mpr (fun h => (I.property h).elim)]
  simp only [HeckeDyadic.norm, Complex.ofReal_natCast, mul_assoc]

def twistedCoefficient (χ : Character) (σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ I.val * (norm I : ℂ)^(-shift σ freq)

theorem twisted_coefficient_summable (χ : Character) (c σ freq : ℝ)
    (hc : 1 < c+σ) :
    Summable (fun I : NonzeroIdeal => ‖twistedCoefficient χ σ freq I‖*(norm I)^(-c)) := by
  have hf := (IdealLogDerivative.mangoldt_weighted_summable_norm
    (idealCoeff χ) (idealCoeff_norm_le_one χ) ((c+σ : ℝ) : ℂ)
    (by simpa using hc)).comp_injective (Subtype.val_injective : Function.Injective
      (fun I : NonzeroIdeal => I.val))
  convert hf using 1
  ext I
  simp only [Function.comp_apply, twistedCoefficient, coefficient, IdealEuler.weighted, IdealEuler.normWeight,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, CubicEisenstein.fullIdealWeight,
    ite_eq_right_iff.mpr (fun h => (I.property h).elim), norm_mul]
  change (‖(IdealMangoldt.value I.val : ℂ)‖ * ‖idealCoeff χ I.val‖ *
      ‖(norm I : ℂ)^(-shift σ freq)‖) * (norm I)^(-c) =
    ‖(IdealMangoldt.value I.val : ℂ)‖ * (‖idealCoeff χ I.val‖ *
      ‖(norm I : ℂ)^(-((c+σ : ℝ) : ℂ))‖)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I),
    Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp only [Complex.neg_re, shift_re, Complex.ofReal_re]
  rw [mul_assoc, mul_assoc, ← Real.rpow_add (norm_pos I)]
  congr 3
  ring

def summand (χ : Character) (W : ℝ → ℂ) (D σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ I.val * W (norm I/D) * ((norm I/D : ℝ) : ℂ)^(-shift σ freq)

def polynomial (χ : Character) (W : ℝ → ℂ) (D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ)) * ∑' I : NonzeroIdeal, summand χ W D σ freq I

theorem twisted_series_eq (χ : Character) (σ freq : ℝ)
    {s : ℂ} (hs : 1 < (s+shift σ freq).re) :
    (∑' I : NonzeroIdeal, twistedCoefficient χ σ freq I*(norm I : ℂ)^(-s)) =
      series χ (s+shift σ freq) := by
  rw [series_eq_tsum χ hs]
  apply tsum_congr
  intro I
  unfold twistedCoefficient
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_pos I).ne')]
  congr 2
  ring

theorem polynomial_eq_weighted (χ : Character) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0 < D) :
    polynomial χ W D σ freq =
      (D : ℂ)^(shift σ freq-(1/2 : ℂ)) *
        ∑' I : NonzeroIdeal, twistedCoefficient χ σ freq I * W (norm I/D) := by
  have he (I : NonzeroIdeal) : summand χ W D σ freq I =
      (D : ℂ)^(shift σ freq) * (twistedCoefficient χ σ freq I * W (norm I/D)) := by
    unfold summand twistedCoefficient
    rw [CompletedGauss.positive_quotient_cpow_neg _ _ (norm_pos I) hD]
    ring
  unfold polynomial
  simp_rw [he]
  rw [tsum_mul_left, ← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 2
  ring

theorem polynomial_mellin (χ : Character) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hWs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (D c σ freq : ℝ) (hD : 0 < D) (hc : 1 < c+σ) :
    polynomial χ W D σ freq = (1/(2*Real.pi) : ℂ)*∫ t : ℝ,
      mellin W ((c : ℂ)+t*Complex.I) *
        (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) *
          series χ (((c : ℂ)+t*Complex.I)+shift σ freq) := by
  rw [polynomial_eq_weighted χ W D σ freq hD]
  rw [CompletedGauss.weightedMellin_inversion norm norm_pos
    (twistedCoefficient χ σ freq) c (twisted_coefficient_summable χ c σ freq hc)
    W a b ha hWs hW D hD]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [twisted_series_eq χ σ freq (by simpa using hc)]
  have he : (D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I) =
      (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
    congr 1
    ring
  calc
    _ = mellin W ((c : ℂ)+t*Complex.I) *
        ((D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I)) *
          series χ (((c : ℂ)+t*Complex.I)+shift σ freq) := by ring
    _ = _ := by rw [he]

end SevenEighths.HeckePrimeDyadic

end

end OAI
