import OAI.NumberTheory.DirichletL.Moments.Amplification

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationLocal
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge ProbePrimePower ProbePhysical
open CenteredMomentUnequal CenteredMomentAmplification CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

def centralLocal (p : O) (hp : p ≠ 0) (n : ℕ) (h : O) : ℂ :=
  sexticGauss (p^(n+1)) (pow_ne_zero _ hp) h / (Ideal.absNorm (Ideal.span {p}) : ℂ)^(n+1)

theorem gauss_unit_scale_norm (a : O) (ha : Supported (Ideal.span {a}))
    (b h : O) (hcop : IsCoprime b a) :
    ‖sexticGauss a (supportedElement_ne_zero a ha) (b*h)‖ =
      ‖sexticGauss a (supportedElement_ne_zero a ha) h‖ := by
  let := finite_quotient_span (supportedElement_ne_zero a ha)
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := CenteredMomentCommonSupport.isUnit_residue_of_coprime a b hcop.symm
  have hn : ‖idealRowHom b (Ideal.span {a})‖ = 1 := by
    change ‖supportedModulusCharacter a ha (Ideal.Quotient.mk _ b)‖ = 1
    rw [← hu]
    exact FiniteRayExpansion.norm_char_unit _ u
  rw [sexticGauss_unit_scale a ha b h hcop,norm_mul,norm_inv,hn,inv_one,one_mul]

theorem primeGauss_actual_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    ‖primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1‖^2 =
      (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := finite_quotient_span hp.ne_zero
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hχ : actualSextic (Ideal.span {p}) hg ≠ 1 := by
    intro he
    have ho := CenteredMomentCanonical.actualSextic_order_six (Ideal.span {p}) hg hc
    rw [he,orderOf_one] at ho
    norm_num at ho
  have ht : (CubicEisenstein.quotientTrace p hp.ne_zero).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero
  have he : primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 =
      gaussSum (actualSextic (Ideal.span {p}) hg) (CubicEisenstein.quotientTrace p hp.ne_zero) := by
    simp [primeGauss,tsum_fintype,gaussSum]
  rw [he,FiniteFieldSieve.primitive_gauss_norm_sq _ _ hχ ht]
  norm_cast
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem centralLocal_six (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    centralLocal p hp.ne_zero 5 (p^6) = 1 - (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ := by
  rw [centralLocal,gauss_prime_power_six p hp hg hc]
  simp only [ite_true]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  field_simp
  ring

theorem centralLocal_seven (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    centralLocal p hp.ne_zero 6 (p^6) =
      primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 /
        (Ideal.absNorm (Ideal.span {p}) : ℂ) := by
  rw [centralLocal,gauss_prime_power_six p hp hg hc]
  simp only [show ¬(6:ℕ)=5 by decide,ite_false,ite_true]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  field_simp
  ring

theorem centralLocal_unit_norm (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (n : ℕ) (h k : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero n (h*k)‖ = ‖centralLocal p hp.ne_zero n k‖ := by
  unfold centralLocal
  rw [norm_div,norm_div,gauss_unit_scale_norm _ (supported_power p hs (n+1)) h k
    ((hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right)]

theorem centralLocal_one_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero 0 h‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ := by
  rw [← mul_one h,centralLocal_unit_norm p hp hs 0 h 1 hph,centralLocal,
    gauss_prime_power_one p hp hg hc]
  simp only [ite_true,zero_add,pow_one,norm_div,Complex.norm_natCast,div_pow,
    primeGauss_actual_norm_sq p hp hg hc]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  field_simp

theorem centralLocal_seven_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero 6 (h*p^6)‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ := by
  rw [centralLocal_unit_norm p hp hs 6 h (p^6) hph,centralLocal_seven p hp hg hc,
    norm_div,Complex.norm_natCast,div_pow,primeGauss_actual_norm_sq p hp hg hc]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  field_simp

theorem centralLocal_six_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero 5 (h*p^6)‖^2 =
      (1 - (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹)^2 := by
  rw [centralLocal_unit_norm p hp hs 5 h (p^6) hph,centralLocal_six p hp hg hc]
  rw [← Complex.ofReal_natCast,← Complex.ofReal_inv,← Complex.ofReal_one,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

end SevenEighths.CenteredMomentAmplificationLocal

end

end OAI
