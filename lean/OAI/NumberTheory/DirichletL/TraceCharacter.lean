import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.FiniteFourier

namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap

namespace SevenEighths.TraceCharacter

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic EisensteinEmbedding ConcreteTraceCRT
open EisensteinSchwartzPoisson FiniteFourier

def traceCharacter (c : O) (hc : c ≠ 0) : AddChar (O ⧸ Ideal.span {c}) ℂ :=
  eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc

theorem traceCharacter_mk (c : O) (hc : c ≠ 0) (x : O) :
    traceCharacter c hc (Ideal.Quotient.mk (Ideal.span {c}) x) =
      ShortDraftTrace.breveE (eisEmbedding x / (eisEmbedding c * eisLam)) := by
  simp only [traceCharacter, eisTraceModChar, IdealGaussCRT.traceModChar_mk]

theorem traceCharacter_eq_paperE (c : O) (hc : c ≠ 0) (x : O) :
    traceCharacter c hc (Ideal.Quotient.mk (Ideal.span {c}) x) =
      paperE (eisEmbedding x / eisEmbedding c) :=
  eisTraceModChar_eq_paperE c hc x

theorem traceCharacter_isPrimitive (c : O) (hc : c ≠ 0) :
    (traceCharacter c hc).IsPrimitive :=
  GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

theorem residue_card :
    Fintype.card (O ⧸ Ideal.span {c}) = Ideal.absNorm (Ideal.span {c}) := by
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

def gaussScalar (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ :=
  gaussSum χ (traceCharacter c (NeZero.ne c))

theorem transform_nonunit (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) (ha : ¬ IsUnit a) :
    (∑ x : O ⧸ Ideal.span {c}, χ x * traceCharacter c (NeZero.ne c) (a * x)) = 0 :=
  gaussSum_mulShift_nonunit_eq_zero χ hχ (traceCharacter c (NeZero.ne c)) ha

theorem transform_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) :
    (∑ x : O ⧸ Ideal.span {c}, χ x * traceCharacter c (NeZero.ne c) (a * x)) =
      χ⁻¹ a * gaussScalar c χ :=
  transform_primitive_character χ hχ (traceCharacter c (NeZero.ne c)) a

theorem paper_transform_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (h : O) :
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      paperE (eisEmbedding (GaussianShiftedPartition.representative c x) *
        eisEmbedding h / eisEmbedding c)) =
      χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) * gaussScalar c χ := by
  simpa only [traceCharacter, eisTraceModChar_frequency] using
    transform_eq c χ hχ (Ideal.Quotient.mk (Ideal.span {c}) h)

theorem gaussScalar_norm_sq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ ^ 2 = (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
  simpa only [gaussScalar, residue_card c] using
    primitive_gaussSum_norm_sq χ hχ (traceCharacter c (NeZero.ne c))
      (traceCharacter_isPrimitive c (NeZero.ne c))

theorem gaussScalar_norm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ = Real.sqrt (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
  rw [← gaussScalar_norm_sq c χ hχ, Real.sqrt_sq (norm_nonneg _)]

theorem gaussScalar_norm_embedding (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ = ‖eisEmbedding c‖ := by
  rw [gaussScalar_norm c χ hχ, ← eisEmbedding_norm_sq_eq_absNorm_span,
    Real.sqrt_sq (norm_nonneg _)]

theorem gaussScalar_ne_zero (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : gaussScalar c χ ≠ 0 :=
  primitive_gaussSum_ne_zero χ hχ (traceCharacter c (NeZero.ne c))
    (traceCharacter_isPrimitive c (NeZero.ne c))

def normalizedGauss (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ :=
  gaussScalar c χ / (‖eisEmbedding c‖ : ℂ)

theorem normalizedGauss_norm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : ‖normalizedGauss c χ‖ = 1 := by
  rw [normalizedGauss, norm_div, gaussScalar_norm_embedding c χ hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))]

theorem character_expansion (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) :
    χ a = (∑ x : O ⧸ Ideal.span {c}, χ⁻¹ x * traceCharacter c (NeZero.ne c) (a * x)) /
      gaussScalar c χ⁻¹ :=
  primitive_character_expansion χ hχ (traceCharacter c (NeZero.ne c))
    (traceCharacter_isPrimitive c (NeZero.ne c)) a

theorem primitive_paper_poisson (f : 𝓢(ℂ, ℂ))
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (gaussScalar c χ / (Ideal.absNorm (Ideal.span {c}) : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  have hp := actual_eisenstein_paper_poisson_trace f c (NeZero.ne c) χ
  change _ = (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      traceCharacter c (NeZero.ne c) (Ideal.Quotient.mk (Ideal.span {c}) h * x)) *
        paperFourier f (eisEmbedding h / eisEmbedding c) at hp
  simp_rw [transform_eq c χ hχ] at hp
  rw [hp, ← tsum_mul_left]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    eisEmbedding_norm_sq_eq_absNorm_span, Complex.ofReal_natCast]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

theorem primitive_radial_paper_poisson (W : 𝓢(ℝ, ℂ)) (scale : ℝ)
    (hscale : 0 < scale) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * gaussScalar c χ / (Ideal.absNorm (Ideal.span {c}) : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (Ideal.span {c}) : ℝ)) := by
  have hp := actual_radial_paper_poisson_trace W scale hscale c (NeZero.ne c) χ
  change _ = (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      traceCharacter c (NeZero.ne c) (Ideal.Quotient.mk (Ideal.span {c}) h * x)) *
        paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [transform_eq c χ hχ, eisEmbedding_norm_sq_eq_absNorm_span c] at hp
  rw [hp, ← tsum_mul_left]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

theorem primitive_radial_paper_poisson_normalized (W : 𝓢(ℝ, ℂ)) (scale : ℝ)
    (hscale : 0 < scale) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * normalizedGauss c χ / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  have hp := primitive_radial_paper_poisson c W scale hscale χ hχ
  rw [← eisEmbedding_norm_sq_eq_absNorm_span c] at hp
  have hnorm : (Ideal.absNorm (Ideal.span {c}) : ℂ) = (‖eisEmbedding c‖ : ℂ) ^ 2 := by
    exact_mod_cast (eisEmbedding_norm_sq_eq_absNorm_span c).symm
  rw [hnorm] at hp
  rw [hp]
  congr 1
  rw [normalizedGauss]
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))
  field_simp

end SevenEighths.TraceCharacter

end

end OAI
