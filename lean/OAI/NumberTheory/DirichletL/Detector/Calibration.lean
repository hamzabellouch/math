import OAI.NumberTheory.DirichletL.Detector.Physical
import Mathlib.Algebra.Group.Pi.Units

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def crtCharacter {ι T : Type*} [Fintype ι] [CommRing T]
    (R : ι → Type*) [∀ i, Field (R i)] (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) : MulChar T ℂ where
  toFun x := ∏ i, χ i (e x i)
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]
  map_nonunit' x hx := by
    have he : ¬∀ i, IsUnit (e x i) := by
      intro h
      apply hx
      have hu := (Pi.isUnit_iff.mpr h).map e.symm.toMonoidHom
      simpa using hu
    obtain ⟨i, hi⟩ := not_forall.mp he
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact (χ i).map_nonunit hi

theorem crtCharacter_pow_six {ι T : Type*} [Fintype ι] [CommRing T]
    (R : ι → Type*) [∀ i, Field (R i)] (e : T ≃+* ∀ i, R i)
    (χ : ∀ i, MulChar (R i) ℂ) (hχ : ∀ i, χ i ^ 6 = 1) :
    crtCharacter R e χ ^ 6 = 1 := by
  apply MulChar.ext
  intro x
  rw [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply x.isUnit]
  change (∏ i, χ i (e x i)) ^ 6 = 1
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  have hu : IsUnit (e x i) := (Pi.isUnit_iff.mp (x.isUnit.map e.toMonoidHom)) i
  have he := congrArg (fun f : MulChar (R i) ℂ => f (e x i)) (hχ i)
  simpa only [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply hu] using he

theorem residue_char_ne_two_of_lambda_mem (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∈ P) : ringChar (O ⧸ P) ≠ 2 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field _
  intro hc
  have hd : goodLambda ∣ (3 : O) :=
    (dvd_pow_self goodLambda (by decide : (2 : ℕ) ≠ 0)).trans lambda_sq_dvd_three
  obtain ⟨k, hk⟩ := hd
  have h3m : (3 : O) ∈ P := by rw [hk]; exact P.mul_mem_right k hg
  have h3 : (3 : O ⧸ P) = 0 := by
    simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr h3m
  have h2 : (2 : O ⧸ P) = 0 := by
    exact (ringChar.spec (O ⧸ P) 2).mpr (by rw [hc])
  have h1 : (1 : O ⧸ P) = 0 := by linear_combination h3 - h2
  exact one_ne_zero h1

theorem exists_local_calibration (P : Ideal O) [P.IsMaximal] :
    ∃ χ : MulChar (O ⧸ P) ℂ, χ ≠ 1 ∧ χ ^ 6 = 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field _
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  by_cases hg : goodLambda ∉ P
  · refine ⟨actualSextic P hg ^ 2, ?_, ?_⟩
    · intro h
      exact ((MulChar.ringHomComp_ne_one_iff eisEmbedding_injective).mpr
        (cubicChar_ne_one P hg)) ((canonicalSextic_pow_two P hg).symm.trans h)
    · calc
        (actualSextic P hg ^ 2) ^ 6 = actualSextic P hg ^ (2 * 6) := (pow_mul _ 2 6).symm
        _ = actualSextic P hg ^ (6 * 2) := rfl
        _ = (actualSextic P hg ^ 6) ^ 2 := pow_mul _ 6 2
        _ = (1 : MulChar (O ⧸ P) ℂ) ^ 2 :=
          congrArg (fun χ : MulChar (O ⧸ P) ℂ => χ ^ 2)
            (CanonicalRowCompletion.actualSextic_sixth_one P hg)
        _ = 1 := one_pow 2
  · have hchar := residue_char_ne_two_of_lambda_mem P (not_not.mp hg)
    let χ : MulChar (O ⧸ P) ℂ := (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom ℂ)
    refine ⟨χ, ?_, ?_⟩
    · exact (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr (quadraticChar_ne_one hchar)
    · have h2 : χ ^ 2 = 1 := by
        dsimp only [χ]
        rw [MulChar.ringHomComp_pow, (quadraticChar_isQuadratic (O ⧸ P)).sq_eq_one,
          MulChar.ringHomComp_one]
      rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, h2, one_pow]

def localCalibration (P : Ideal O) [P.IsMaximal] : MulChar (O ⧸ P) ℂ :=
  Classical.choose (exists_local_calibration P)

theorem localCalibration_nonprincipal (P : Ideal O) [P.IsMaximal] :
    localCalibration P ≠ 1 := (Classical.choose_spec (exists_local_calibration P)).1

theorem localCalibration_pow_six (P : Ideal O) [P.IsMaximal] :
    localCalibration P ^ 6 = 1 := (Classical.choose_spec (exists_local_calibration P)).2

def calibrationFromPrimes {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) : CalibrationData := by
  letI (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  exact {
    excluded := Finset.univ.image P
    generator := finitePrimeModulus P
    generator_ne_zero := finitePrimeModulus_ne_zero P
    residue := crtCharacter (fun i => O ⧸ P i)
      ((Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
        (IdealGaussCRT.quotientProdEquivPi P hcop)) (fun i => localCalibration (P i)) }

theorem calibrationFromPrimes_pow_six {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    (calibrationFromPrimes P hcop).residue ^ 6 = 1 := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  exact crtCharacter_pow_six _ _ _ (fun i => localCalibration_pow_six (P i))

theorem calibrationFromPrimes_tau_norm {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    ‖(calibrationFromPrimes P hcop).tau‖ = 1 := by
  let b := finitePrimeModulus P
  have hb : b ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {b}) := ConcreteTraceCRT.finite_quotient_span hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let e : (O ⧸ Ideal.span {b}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let ψ := quotientTrace b hb
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive b hb
  have hg := IdealGaussCRT.norm_gauss_finite_crt_sq (fun i => O ⧸ P i) e
    (fun i => localCalibration (P i)) ψ (fun i => localCalibration_nonprincipal (P i))
    (fun i => IdealGaussCRT.coordinateAddChar_isPrimitive _ e ψ hψ i)
  have hcard : (Fintype.card (O ⧸ Ideal.span {b}) : ℝ) = elementNorm b := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hcard] at hg
  have hQ : 0 < elementNorm b := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hb))
  have hn : ‖∑ x : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e x i)) * ψ x‖ =
      Real.sqrt (elementNorm b) := by
    have hs := Real.sq_sqrt hQ.le
    have hs0 := Real.sqrt_nonneg (elementNorm b)
    have hn0 := norm_nonneg (∑ x : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e x i)) * ψ x)
    nlinarith
  change ‖(∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) * ψ d) /
    (Real.sqrt (elementNorm b) : ℂ)‖ = 1
  rw [tsum_fintype, norm_div, hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_self (Real.sqrt_pos.mpr hQ).ne']

theorem calibrationFromPrimes_tau_ne_zero {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) :
    (calibrationFromPrimes P hcop).tau ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [calibrationFromPrimes_tau_norm]; norm_num)

def calibrationForSet (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) : CalibrationData := by
  letI (P : S) : P.val.IsMaximal := hS P.val P.property
  exact calibrationFromPrimes (fun P : S => P.val)
    (fun P Q hPQ => Ideal.isCoprime_of_isMaximal (fun h => hPQ (Subtype.ext h)))

theorem calibrationForSet_excluded (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).excluded = S := by
  change Finset.univ.image (fun P : S => P.val) = S
  ext P
  simp

theorem calibrationForSet_span (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    Ideal.span {(calibrationForSet S hS).generator} = ∏ P ∈ S, P := by
  change Ideal.span {finitePrimeModulus (fun P : S => P.val)} = _
  rw [span_finitePrimeModulus]
  exact Finset.prod_coe_sort S (fun P : Ideal O => P)

theorem calibrationForSet_pow_six (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).residue ^ 6 = 1 := by
  let (P : S) : P.val.IsMaximal := hS P.val P.property
  unfold calibrationForSet
  apply calibrationFromPrimes_pow_six

theorem calibrationForSet_tau_norm (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    ‖(calibrationForSet S hS).tau‖ = 1 := by
  let (P : S) : P.val.IsMaximal := hS P.val P.property
  unfold calibrationForSet
  apply calibrationFromPrimes_tau_norm

theorem calibrationForSet_tau_ne_zero (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal) :
    (calibrationForSet S hS).tau ≠ 0 := by
  exact norm_ne_zero_iff.mp (by rw [calibrationForSet_tau_norm]; norm_num)

end SevenEighths.ProbePhysical
end

end OAI
