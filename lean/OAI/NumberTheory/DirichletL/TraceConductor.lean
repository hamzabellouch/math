import OAI.NumberTheory.DirichletL.TraceCharacter
import OAI.NumberTheory.DirichletL.ConductorPresentation

namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap Classical

namespace SevenEighths.TraceConductor

abbrev O := ActualEisensteinCubic.O

open FiniteFourier CharacterTransport ConcretePrimeRowBridge
open ConcreteTraceCRT EisensteinSchwartzPoisson

structure PrimitivePresentation (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ) where
  generator : O
  generator_ne_zero : generator ≠ 0
  character : MulChar (O ⧸ Ideal.span {generator}) ℂ
  primitive : IsPrimitiveOnIdeals character
  modulus_le : M ≤ Ideal.span {generator}
  norm_le : Ideal.absNorm (Ideal.span {generator}) ≤ M.absNorm
  source_mask : ∀ a : O, χ (Ideal.Quotient.mk M a) =
    if IsUnit (Ideal.Quotient.mk M a) then
      character (Ideal.Quotient.mk (Ideal.span {generator}) a) else 0

theorem exists_primitivePresentation (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ) : Nonempty (PrimitivePresentation M χ) := by
  let : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  obtain ⟨K, φ, hMK, hK, hφ, hnorm, hmask⟩ :=
    ConductorPresentation.exists_primitive_presentation M χ
  let c := idealGenerator K
  let e : (O ⧸ Ideal.span {c}) ≃+* (O ⧸ K) :=
    Ideal.quotEquivOfEq (span_idealGenerator K)
  let θ := pullback e φ
  refine ⟨{
    generator := c
    generator_ne_zero := idealGenerator_ne_zero K hK
    character := θ
    primitive := primitive_pullback e φ hφ
    modulus_le := ?_
    norm_le := ?_
    source_mask := ?_ }⟩
  · simpa only [c, span_idealGenerator] using hMK
  · simpa only [c, span_idealGenerator] using hnorm
  · intro a
    simpa only [θ, pullback_apply, e, Ideal.quotEquivOfEq_mk] using hmask a

def primitivePresentation (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ) : PrimitivePresentation M χ :=
  Classical.choice (exists_primitivePresentation M hM χ)

namespace PrimitivePresentation

variable {M : Ideal O} {χ : MulChar (O ⧸ M) ℂ}

def conductor (P : PrimitivePresentation M χ) : Ideal O := Ideal.span {P.generator}

theorem conductor_ne_bot (P : PrimitivePresentation M χ) : P.conductor ≠ ⊥ := by
  intro h
  exact P.generator_ne_zero (Ideal.span_singleton_eq_bot.mp h)

def gauss (P : PrimitivePresentation M χ) : ℂ := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.gaussScalar P.generator P.character

theorem gauss_norm (P : PrimitivePresentation M χ) :
    ‖P.gauss‖ = Real.sqrt (P.conductor.absNorm : ℝ) := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.gaussScalar_norm P.generator P.character P.primitive

theorem gauss_ne_zero (P : PrimitivePresentation M χ) : P.gauss ≠ 0 := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.gaussScalar_ne_zero P.generator P.character P.primitive

def fourier (P : PrimitivePresentation M χ) (a : O ⧸ P.conductor) : ℂ := by
  let : Finite (O ⧸ Ideal.span {P.generator}) := finite_quotient_span P.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {P.generator}) := Fintype.ofFinite _
  exact transform (TraceCharacter.traceCharacter P.generator P.generator_ne_zero) P.character a

theorem fourier_eq (P : PrimitivePresentation M χ) (a : O ⧸ P.conductor) :
    P.fourier a = P.character⁻¹ a * P.gauss := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.transform_eq P.generator P.character P.primitive a

theorem fourier_nonunit (P : PrimitivePresentation M χ) (a : O ⧸ P.conductor)
    (ha : ¬ IsUnit a) : P.fourier a = 0 := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.transform_nonunit P.generator P.character P.primitive a ha

theorem source_sum_eq_masked (P : PrimitivePresentation M χ) (f : O → ℂ) :
    (∑' a : O, χ (Ideal.Quotient.mk M a) * f a) =
      ∑' a : O, (if IsUnit (Ideal.Quotient.mk M a) then
        P.character (Ideal.Quotient.mk P.conductor a) else 0) * f a := by
  apply tsum_congr
  intro a
  rw [P.source_mask]
  rfl

def normalizedGauss (P : PrimitivePresentation M χ) : ℂ := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.normalizedGauss P.generator P.character

theorem normalizedGauss_norm (P : PrimitivePresentation M χ) :
    ‖P.normalizedGauss‖ = 1 := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.normalizedGauss_norm P.generator P.character P.primitive

theorem paper_poisson (P : PrimitivePresentation M χ) (f : 𝓢(ℂ, ℂ)) :
    (∑' z : O, P.character (Ideal.Quotient.mk P.conductor z) * f (eisEmbedding z)) =
      (P.gauss / (P.conductor.absNorm : ℂ)) *
        ∑' h : O, P.character⁻¹ (Ideal.Quotient.mk P.conductor h) *
          paperFourier f (eisEmbedding h / eisEmbedding P.generator) := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.primitive_paper_poisson P.generator f P.character P.primitive

theorem radial_paper_poisson (P : PrimitivePresentation M χ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, P.character (Ideal.Quotient.mk P.conductor z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * P.normalizedGauss / (‖eisEmbedding P.generator‖ : ℂ)) *
        ∑' h : O, P.character⁻¹ (Ideal.Quotient.mk P.conductor h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding P.generator‖ ^ 2) := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.primitive_radial_paper_poisson_normalized
    P.generator W scale hscale P.character P.primitive

end PrimitivePresentation

end SevenEighths.TraceConductor

end

end OAI
