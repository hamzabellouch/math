import OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion
import OAI.NumberTheory.DirichletL.Moments.RayNonprincipal

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlot
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
local notation "O" => HeckeFamily.O

def primePool (M:Ideal O) (H:Subgroup (O⧸M)ˣ) (b D:ℝ) : Finset (Ideal O) :=
  (annulusSet b D).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H)

def slotProfile (W:ℝ→ℂ) (D σ:ℝ) (I:Ideal O) : ℂ := annularWeight W D σ 0 I

lemma norm_height_split (N D σ t:ℝ) (hN:0<N) (hD:0<D) :
    (((N/D:ℝ):ℂ)^(-shift σ 0))*(N:ℂ)^(Complex.I*t)=
      (D:ℂ)^(Complex.I*t)*((N/D:ℝ):ℂ)^(-shift σ t) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    ←Complex.ofReal_log (div_pos hN hD).le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log hD.le,Real.log_div hN.ne' hD.ne',←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [HeckeDyadic.shift,Complex.ofReal_sub,Complex.ofReal_zero,zero_mul,sub_zero]
  ring

lemma sqrt_inverse_cpow (D:ℝ) (hD:0<D) :
    (Real.sqrt D:ℂ)⁻¹=(D:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hD.le (1/2:ℝ))

theorem normalizedSlot_eq_ray (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t:ℝ) (hD:0<D) :
    normalizedSlot η m A z (primePool M H b D) (slotProfile W D σ) t D=
      (D:ℂ)^(Complex.I*t)*rayPrimePolynomial M H χ W b D σ t := by
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
    ((W ((I.absNorm:ℝ)/D)*(((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ 0))*idealCoeff χ I*
      (I.absNorm:ℂ)^(Complex.I*t))=_
  have hn:=norm_height_split (I.absNorm:ℝ) D σ t hN hD
  simp only [Complex.ofReal_natCast] at hn
  calc
    _=(D:ℂ)^(-(1/2:ℂ))*(W ((I.absNorm:ℝ)/D)*idealCoeff χ I)*
      ((((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ 0)*(I.absNorm:ℂ)^(Complex.I*t)) := by ring
    _=_ := by rw [hn]; unfold annularWeight; ring

theorem normalizedSlot_norm_sq (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t:ℝ) (hD:0<D) :
    ‖normalizedSlot η m A z (primePool M H b D) (slotProfile W D σ) t D‖^2=
      ‖rayPrimePolynomial M H χ W b D σ t‖^2 := by
  rw [normalizedSlot_eq_ray M H η χ m A z hrow W b D σ t hD,norm_mul,
    norm_real_imaginary_power D t hD,one_mul]

end SevenEighths.CenteredMomentPrimeSlot

end

end OAI
