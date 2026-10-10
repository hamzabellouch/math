import OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
import OAI.NumberTheory.DirichletL.Moments.GaussEnergy
import OAI.NumberTheory.DirichletL.Moments.Primitive

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstNormalization
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CenteredMomentCommonSupport CenteredMomentFourier
open CenteredMomentSupportedCorrelation CenteredMomentFirstReduced CenteredMomentFirstActiveFourier
open CenteredMomentGaussEnergy CenteredMomentPrimitive CenteredMomentFirstPoisson
local notation "O" => ActualEisensteinCubic.O

theorem residueGauss_eq_norm_mul_gaussRow (a : O) (ha : Supported (Ideal.span {a})) (h : O) :
    residueGauss a (supported_element_ne_zero a ha) (supportedModulusCharacter a ha) (Ideal.Quotient.mk _ h)=
      (‖eisEmbedding a‖:ℂ)*gaussRow a ha h := by
  have hn : (‖eisEmbedding a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero a ha)))
  rw [gaussRow,residueGauss_supported_mk,sqrt_absNorm]
  field_simp

theorem normalized_active_coefficient {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i,(P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ P i)
    (hchar : ∀ i,ringChar (O ⧸ P i)≠2)
    (j : ι → ℕ) (hj0 : ∀ i,j i≠0) (hj6 : ∀ i,j i<6)
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (har : IsCoprime a (b*finitePrimeModulus P)) (hbr : IsCoprime b (finitePrimeModulus P))
    (h : O) :
    let r := finitePrimeModulus P
    let G := principalSexticRow P hcop hg j r (span_finitePrimeModulus P)
    tripleFourier a b r (supported_element_ne_zero a ha) (supported_element_ne_zero b hb)
      (finitePrimeModulus_ne_zero P) (supportedModulusCharacter a ha) (supportedModulusCharacter b hb)⁻¹ G h /
      (‖eisEmbedding (a*(b*r))‖^2:ℝ) =
      (canonicalNormalizedGauss P hcop hg j /
        ((‖eisEmbedding a‖:ℂ)*(‖eisEmbedding b‖:ℂ)*(‖eisEmbedding r‖:ℂ)))*
      (CanonicalRowCompletion.idealRowHom (b*r) (Ideal.span {a})*
        star (CanonicalRowCompletion.idealRowHom (a*r) (Ideal.span {b}))*finiteSexticRow P hg j (a*b))*
      (star (finiteSexticRow P hg j h)*gaussRow a ha h*star (gaussRow b hb (-h))) := by
  dsimp only
  let := finite_quotient_span (supported_element_ne_zero b hb)
  have hna : (‖eisEmbedding a‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero a ha)))
  have hnb : (‖eisEmbedding b‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (supported_element_ne_zero b hb)))
  have hnr : (‖eisEmbedding (finitePrimeModulus P)‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P)))
  rw [tripleFourier_active P hcop hg hchar j hj0 hj6 a b
    (supported_element_ne_zero a ha) (supported_element_ne_zero b hb) har hbr,
    residueGauss_inverse,← map_neg,residueGauss_eq_norm_mul_gaussRow a ha,
    residueGauss_eq_norm_mul_gaussRow b hb,← MulChar.star_apply',
    supportedModulusCharacter_mk,supportedModulusCharacter_mk]
  simp only [canonicalNormalizedGauss,map_mul,norm_mul,star_mul,Complex.star_def,
    Complex.conj_ofReal,Complex.ofReal_pow,Complex.ofReal_mul]
  field_simp

end SevenEighths.CenteredMomentFirstNormalization

end

end OAI
