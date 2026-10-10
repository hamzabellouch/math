import OAI.NumberTheory.DirichletL.Hecke.Dyadic
import OAI.NumberTheory.DirichletL.Hecke.StripActual

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

private instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
private instance : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def twistedCoefficient (χ : Character) (inverse : Bool) (σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ inverse I.val * (norm I : ℂ)^(-shift σ freq)

theorem twisted_coefficient_summable (χ : Character) (inverse : Bool) (c σ freq : ℝ)
    (hc : 1 < c+σ) :
    Summable (fun I : NonzeroIdeal => ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c)) := by
  have hf := (CubicEisenstein.fullIdealWeight_summable_norm ((c+σ : ℝ) : ℂ)
    (by simpa using hc)).comp_injective (Subtype.val_injective : Function.Injective
      (fun I : NonzeroIdeal => I.val))
  apply hf.of_nonneg_of_le (fun I => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_pos I).le _))
  intro I
  have hI : I.val ≠ 0 := I.property
  change ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c) ≤
    ‖CubicEisenstein.fullIdealWeight ((c+σ : ℝ) : ℂ) I.val‖
  rw [CubicEisenstein.fullIdealWeight, ite_eq_right hI]
  change ‖twistedCoefficient χ inverse σ freq I‖*(norm I)^(-c) ≤
    ‖(norm I : ℂ)^(-((c+σ : ℝ) : ℂ))‖
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I)]
  simp only [Complex.neg_re, Complex.ofReal_re]
  unfold twistedCoefficient
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos I), Complex.neg_re, shift_re]
  calc
    _ = ‖coefficient χ inverse I.val‖ * (norm I)^(-(c+σ)) := by
      rw [mul_assoc, ← Real.rpow_add (norm_pos I)]
      congr 2
      ring
    _ ≤ _ := mul_le_of_le_one_left (Real.rpow_nonneg (norm_pos I).le _)
      (coefficient_norm_le χ inverse I.val)

theorem twisted_series_eq (χ : Character) (inverse : Bool) (σ freq : ℝ)
    {s : ℂ} (hs : 1 < (s+shift σ freq).re) :
    (∑' I : NonzeroIdeal, twistedCoefficient χ inverse σ freq I*(norm I : ℂ)^(-s)) =
      series χ inverse (s+shift σ freq) := by
  rw [series_eq_tsum χ inverse hs]
  apply tsum_congr
  intro I
  unfold twistedCoefficient
  rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_pos I).ne')]
  congr 2
  ring

theorem polynomial_eq_weighted (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0 < D) :
    polynomial χ inverse W D σ freq =
      (D : ℂ)^(shift σ freq-(1/2 : ℂ)) *
        ∑' I : NonzeroIdeal, twistedCoefficient χ inverse σ freq I * W (norm I/D) := by
  have he (I : NonzeroIdeal) : summand χ inverse W D σ freq I =
      (D : ℂ)^(shift σ freq) * (twistedCoefficient χ inverse σ freq I * W (norm I/D)) := by
    unfold summand twistedCoefficient
    rw [CompletedGauss.positive_quotient_cpow_neg _ _ (norm_pos I) hD]
    ring
  unfold polynomial
  simp_rw [he]
  rw [tsum_mul_left, ← mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
  congr 2
  ring

theorem polynomial_mellin (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hWs : Function.support W ⊆ Icc a b)
    (hW : ContDiff ℝ ∞ W) (D c σ freq : ℝ) (hD : 0 < D) (hc : 1 < c+σ) :
    polynomial χ inverse W D σ freq = (1/(2*Real.pi) : ℂ)*∫ t : ℝ,
      mellin W ((c : ℂ)+t*Complex.I) *
        (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) *
          series χ inverse (((c : ℂ)+t*Complex.I)+shift σ freq) := by
  rw [polynomial_eq_weighted χ inverse W D σ freq hD]
  rw [CompletedGauss.weightedMellin_inversion norm norm_pos
    (twistedCoefficient χ inverse σ freq) c (twisted_coefficient_summable χ inverse c σ freq hc)
    W a b ha hWs hW D hD]
  rw [mul_left_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [twisted_series_eq χ inverse σ freq (by simpa using hc)]
  have he : (D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I) =
      (D : ℂ)^(((c : ℂ)+t*Complex.I)+shift σ freq-(1/2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hD.ne')]
    congr 1
    ring
  calc
    _ = mellin W ((c : ℂ)+t*Complex.I) *
        ((D : ℂ)^(shift σ freq-(1/2 : ℂ))*(D : ℂ)^((c : ℂ)+t*Complex.I)) *
          series χ inverse (((c : ℂ)+t*Complex.I)+shift σ freq) := by ring
    _ = _ := by rw [he]

end SevenEighths.HeckeDyadic

end

end OAI
