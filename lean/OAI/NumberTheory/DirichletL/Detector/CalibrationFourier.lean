import OAI.NumberTheory.DirichletL.Detector.Calibration

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def calibrationGauss (C : CalibrationData) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {C.generator}, C.residue d *
    quotientTrace C.generator C.generator_ne_zero
      (Ideal.Quotient.mk (Ideal.span {C.generator}) h * d)

theorem calibrationGauss_one (C : CalibrationData) :
    calibrationGauss C 1 = (Real.sqrt (elementNorm C.generator) : ℂ) * C.tau := by
  have hn : 0 < elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hc : (Real.sqrt (elementNorm C.generator) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
  simp only [calibrationGauss, map_one, one_mul, CalibrationData.tau]
  field_simp

theorem calibrationFromPrimes_gauss {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P)) (h : O) :
    calibrationGauss (calibrationFromPrimes P hcop) h =
      ((calibrationFromPrimes P hcop).residueMonoid h)⁻¹ *
        calibrationGauss (calibrationFromPrimes P hcop) 1 := by
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
  have ht := IdealGaussCRT.gauss_transform_finite_crt_scalar (fun i => O ⧸ P i) e
    (fun i => localCalibration (P i)) ψ (fun i => localCalibration_nonprincipal (P i))
    (Ideal.Quotient.mk (Ideal.span {b}) h)
  change (∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) *
      ψ (Ideal.Quotient.mk (Ideal.span {b}) h * d)) =
    (∏ i, localCalibration (P i) (e (Ideal.Quotient.mk (Ideal.span {b}) h) i))⁻¹ *
      ∑' d : O ⧸ Ideal.span {b}, (∏ i, localCalibration (P i) (e d i)) *
        ψ (Ideal.Quotient.mk (Ideal.span {b}) 1 * d)
  simpa only [tsum_fintype, map_one, one_mul] using ht

theorem calibrationForSet_gauss (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (h : O) :
    calibrationGauss (calibrationForSet S hS) h =
      star ((calibrationForSet S hS).residueMonoid h) *
        (Real.sqrt (elementNorm (calibrationForSet S hS).generator) : ℂ) *
        (calibrationForSet S hS).tau := by
  let C := calibrationForSet S hS
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  have hc : star (C.residueMonoid h) = (C.residueMonoid h)⁻¹ := by
    exact (MulChar.star_apply' C.residue (Ideal.Quotient.mk _ h)).trans
      (MulChar.inv_apply_eq_inv' _ _)
  have he : calibrationGauss C h = (C.residueMonoid h)⁻¹ * calibrationGauss C 1 := by
    let (P : S) : P.val.IsMaximal := hS P.val P.property
    unfold C calibrationForSet
    apply calibrationFromPrimes_gauss
  rw [he, calibrationGauss_one, ← hc]
  ring

theorem calibrationForSet_residue_sixth (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) (ha : IsCoprime (calibrationForSet S hS).generator a) :
    (calibrationForSet S hS).residueMonoid a ^ 6 = 1 := by
  let C := calibrationForSet S hS
  have hu := (isUnit_quotient_span_iff C.generator a).mpr ha
  have h6 := congrArg (fun χ : MulChar (O ⧸ Ideal.span {C.generator}) ℂ =>
    χ (Ideal.Quotient.mk _ a)) (calibrationForSet_pow_six S hS)
  change C.residue (Ideal.Quotient.mk _ a) ^ 6 = 1
  simpa only [MulChar.pow_apply' _ (by decide : (6 : ℕ) ≠ 0), MulChar.one_apply hu] using h6

theorem calibrationForSet_quotient_conjugate (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (s k u a : O)
    (hs : IsCoprime (calibrationForSet S hS).generator s)
    (ha : IsCoprime (calibrationForSet S hS).generator a)
    (hrel : s * k = u * a ^ 6) :
    star ((calibrationForSet S hS).residueMonoid k) =
      star ((calibrationForSet S hS).residueMonoid u) *
        (calibrationForSet S hS).residueMonoid s := by
  let C := calibrationForSet S hS
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  have hc (x : O) : star (C.residueMonoid x) = (C.residueMonoid x)⁻¹ := by
    exact (MulChar.star_apply' C.residue (Ideal.Quotient.mk _ x)).trans
      (MulChar.inv_apply_eq_inv' _ _)
  have hu := (isUnit_quotient_span_iff C.generator s).mpr hs
  have hsn : C.residueMonoid s ≠ 0 := C.residue.apply_ne_zero_iff.mpr hu
  have he := congrArg C.residueMonoid hrel
  simp only [map_mul, map_pow] at he
  have h6 : C.residueMonoid a ^ 6 = 1 := calibrationForSet_residue_sixth S hS a ha
  rw [h6, mul_one] at he
  have hk : C.residueMonoid k = (C.residueMonoid s)⁻¹ * C.residueMonoid u := by
    rw [← he, ← mul_assoc, inv_mul_cancel₀ hsn, one_mul]
  change star (C.residueMonoid k) = star (C.residueMonoid u) * C.residueMonoid s
  rw [hc k, hc u, hk, mul_inv_rev, inv_inv]

theorem calibrationForSet_gauss_sixth_row (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (s k u a : O)
    (hs : IsCoprime (calibrationForSet S hS).generator s)
    (ha : IsCoprime (calibrationForSet S hS).generator a)
    (hrel : s * k = u * a ^ 6) :
    calibrationGauss (calibrationForSet S hS) k =
      star ((calibrationForSet S hS).residueMonoid u) *
        (calibrationForSet S hS).residueMonoid s *
        (Real.sqrt (elementNorm (calibrationForSet S hS).generator) : ℂ) *
        (calibrationForSet S hS).tau := by
  rw [calibrationForSet_gauss,
    calibrationForSet_quotient_conjugate S hS s k u a hs ha hrel]

end SevenEighths.ProbePhysical
end

end OAI
