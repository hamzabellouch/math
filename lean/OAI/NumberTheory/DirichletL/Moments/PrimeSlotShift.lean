import OAI.NumberTheory.DirichletL.Moments.PrimeSlot

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlotShift
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
open CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma norm_height_split (N D σ t v:ℝ) (hN:0<N) (hD:0<D) :
    (((N/D:ℝ):ℂ)^(-shift σ v))*(N:ℂ)^(Complex.I*t)=
      (D:ℂ)^(Complex.I*t)*((N/D:ℝ):ℂ)^(-shift σ (t+v)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    ←Complex.ofReal_log (div_pos hN hD).le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log hD.le,Real.log_div hN.ne' hD.ne',←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [HeckeDyadic.shift,Complex.ofReal_sub,Complex.ofReal_add]
  ring

theorem normalizedSlot_eq_ray (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t v:ℝ) (hD:0<D) :
    normalizedSlot η m A z (primePool M H b D) (annularWeight W D σ v) t D=
      (D:ℂ)^(Complex.I*t)*rayPrimePolynomial M H χ W b D σ (t+v) := by
  unfold normalizedSlot rowSlot rayPrimePolynomial primePool
  rw [sqrt_inverse_cpow D hD]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hp:Prime I := (Finset.mem_filter.mp hI).2.1
  have hN:0<(I.absNorm:ℝ) := norm_pos ⟨I,hp.ne_zero⟩
  have hc:=idealCoeff_eq_row η χ m 1 (A*z) hrow I
  simp only [one_pow,mul_one] at hc
  rw [←hc]
  change (D:ℂ)^(-(1/2:ℂ))*
    ((W ((I.absNorm:ℝ)/D)*(((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ v))*idealCoeff χ I*
      (I.absNorm:ℂ)^(Complex.I*t))=_
  have hn:=norm_height_split (I.absNorm:ℝ) D σ t v hN hD
  simp only [Complex.ofReal_natCast] at hn
  calc
    _=(D:ℂ)^(-(1/2:ℂ))*(W ((I.absNorm:ℝ)/D)*idealCoeff χ I)*
      ((((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ v)*(I.absNorm:ℂ)^(Complex.I*t)) := by ring
    _=_ := by rw [hn]; unfold annularWeight; ring

theorem normalizedSlot_norm_sq (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t v:ℝ) (hD:0<D) :
    ‖normalizedSlot η m A z (primePool M H b D) (annularWeight W D σ v) t D‖^2=
      ‖rayPrimePolynomial M H χ W b D σ (t+v)‖^2 := by
  rw [normalizedSlot_eq_ray M H η χ m A z hrow W b D σ t v hD,norm_mul,
    norm_real_imaginary_power D t hD,one_mul]

end SevenEighths.CenteredMomentPrimeSlotShift

end

end OAI
