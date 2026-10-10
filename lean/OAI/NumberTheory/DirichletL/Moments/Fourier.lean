import OAI.NumberTheory.DirichletL.Moments.Support
import OAI.NumberTheory.DirichletL.Detector.Physical

namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentFourier
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation

def frequencyReduction (d m : O) (h : d ∣ m) : Residue m →+* Residue d :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr h)

@[simp] theorem frequencyReduction_mk (d m : O) (h : d ∣ m) (x : O) :
    frequencyReduction d m h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

theorem quotientTrace_scaled (d a m : O) (hm : m = d * a)
    (hd : d ≠ 0) (ha : a ≠ 0) (hm0 : m ≠ 0)
    (h : Residue m) (x : Residue d) :
    quotientTrace m hm0 (h * scaledResidue d a m hm x) =
      quotientTrace d hd (frequencyReduction d m (hm ▸ dvd_mul_right d a) h * x) := by
  subst m
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective h
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ht := quotientTrace_conductor_scale d a h hd ha (Ideal.Quotient.mk _ x)
  simp only [scaledResidue_mk, frequencyReduction_mk, ← map_mul]
  simpa only [← map_mul, conductorReduction, Ideal.Quotient.factor_mk, mul_assoc,
    mul_left_comm, mul_comm] using ht

def residueGauss (d : O) (hd : d ≠ 0) (χ : MulChar (Residue d) ℂ)
    (h : Residue d) : ℂ :=
  ∑' x : Residue d, χ x * quotientTrace d hd (h * x)

theorem residueGauss_supported_mk (d : O)
    (hd : CanonicalQuadraticSieve.Supported (Ideal.span {d})) (h : O) :
    residueGauss d (supported_element_ne_zero d hd) (supportedModulusCharacter d hd)
      (Ideal.Quotient.mk _ h) = ProbePhysical.sexticGauss d (supported_element_ne_zero d hd) h := by
  apply tsum_congr
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [supportedModulusCharacter_mk, ProbePhysical.sexticGauss_coefficient_mk]

theorem fourierSum_scaled (d a m : O) (hm : m = d * a)
    (hd : d ≠ 0) (ha : a ≠ 0) (hm0 : m ≠ 0)
    [Fintype (Residue d)] (χ : MulChar (Residue d) ℂ) (h : Residue m) :
    fourierSum (quotientTrace m hm0) (scaledResidue d a m hm) χ h =
      residueGauss d hd χ (frequencyReduction d m (hm ▸ dvd_mul_right d a) h) := by
  simp only [fourierSum, residueGauss, tsum_fintype, quotientTrace_scaled d a m hm hd ha hm0]

theorem actual_gauss_correlation (u v : O) (hu : u ≠ 0) (hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)] [Fintype (Residue (u * v))]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : O) :
    (∑ h : Residue (u * v),
      residueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
        star (residueGauss v hv χv (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
          quotientTrace (u * v) (mul_ne_zero hu hv) (-(h * Ideal.Quotient.mk _ j))) =
      (Fintype.card (Residue (u * v)) : ℂ) * fullModulusCorrelation u v χu χv j := by
  have h := fullModulusCorrelation_fourier u v χu χv j
    (quotientTrace (u * v) (mul_ne_zero hu hv))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive _ _)
  simp_rw [fourierSum_scaled u v (u * v) rfl hu hv (mul_ne_zero hu hv),
    fourierSum_scaled v u (u * v) (mul_comm u v) hv hu (mul_ne_zero hu hv)] at h
  exact h

def normalizedResidueGauss (d : O) (hd : d ≠ 0) (χ : MulChar (Residue d) ℂ)
    (h : Residue d) : ℂ :=
  residueGauss d hd χ h / (Real.sqrt (Ideal.absNorm (Ideal.span {d}) : ℝ) : ℂ)

theorem normalized_gauss_correlation (u v : O) (hu : u ≠ 0) (hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)] [Fintype (Residue (u * v))]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : O) :
    fullModulusCorrelation u v χu χv j =
      ((Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ))⁻¹ *
      ∑ h : Residue (u * v),
        normalizedResidueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
          star (normalizedResidueGauss v hv χv
            (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
          quotientTrace (u * v) (mul_ne_zero hu hv) (-(h * Ideal.Quotient.mk _ j)) := by
  let ru : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ)
  let rv : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ)
  have hqu : (0 : ℝ) < Ideal.absNorm (Ideal.span {u}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hu))
  have hqv : (0 : ℝ) < Ideal.absNorm (Ideal.span {v}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hv))
  have hru : ru ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hqu).ne'
  have hrv : rv ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hqv).ne'
  have hsqu : ru ^ 2 = (Ideal.absNorm (Ideal.span {u}) : ℂ) := by
    dsimp only [ru]
    exact_mod_cast Real.sq_sqrt hqu.le
  have hsqv : rv ^ 2 = (Ideal.absNorm (Ideal.span {v}) : ℂ) := by
    dsimp only [rv]
    exact_mod_cast Real.sq_sqrt hqv.le
  have hcard : (Fintype.card (Residue (u * v)) : ℂ) = (ru * rv) ^ 2 := by
    have hc : Fintype.card (Residue (u * v)) = Ideal.absNorm (Ideal.span {u * v}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    rw [hc, ← Ideal.span_singleton_mul_span_singleton, map_mul, Nat.cast_mul,
      ← hsqu, ← hsqv, mul_pow]
  have hterm (h : Residue (u * v)) :
      normalizedResidueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
        star (normalizedResidueGauss v hv χv
          (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
        quotientTrace (u * v) (mul_ne_zero hu hv) (-(h * Ideal.Quotient.mk _ j)) =
      (residueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
        star (residueGauss v hv χv (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
        quotientTrace (u * v) (mul_ne_zero hu hv) (-(h * Ideal.Quotient.mk _ j))) / (ru * rv) := by
    simp only [normalizedResidueGauss, star_div₀, Complex.star_def, Complex.conj_ofReal]
    dsimp only [ru, rv]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, actual_gauss_correlation u v hu hv χu χv j, hcard]
  change _ = (ru * rv)⁻¹ * ((ru * rv) ^ 2 * _ / (ru * rv))
  field_simp

end SevenEighths.CenteredMomentFourier
end

end OAI
