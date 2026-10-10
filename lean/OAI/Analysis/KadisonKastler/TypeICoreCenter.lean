import OAI.Analysis.KadisonKastler.TracialCornerCoreCenter
import OAI.Analysis.KadisonKastler.TypeICyclicRepresentation
import OAI.Analysis.KadisonKastler.TypeIFactorStability

namespace OAI

/-! # A minimal projection in the source prevents a factorial modular core -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem minimal_corner_vector_tracial (p : AlgebraProjection M)
    (hp : IsMinimalProjectionIn M p) (Ω : H) (a b : Algebra M) :
    inner ℂ Ω ((p.val * a * p.val * b * p.val).val Ω) =
      inner ℂ Ω ((p.val * b * p.val * a * p.val).val Ω) := by
  have hproduct (a b : Algebra M) : (p.val * a * p.val) * (p.val * b * p.val) =
      p.val * a * p.val * b * p.val := by
    calc
      _ = (p.val * a * p.val * p.val) * b * p.val := by simp only [mul_assoc]
      _ = _ := by rw [mul_assoc (p.val * a) p.val p.val, p.property.isIdempotentElem.eq]
  obtain ⟨z, hz⟩ := Generator.Tracial.corner_scalar_of_projections p
    (fun q hq => (hp.2 q hq).imp id (congrArg Subtype.val)) (p.val * a * p.val)
    (by simp only [← mul_assoc, p.property.isIdempotentElem.eq])
    (by rw [mul_assoc (p.val * a) p.val p.val, p.property.isIdempotentElem.eq])
  have hl : p.val * (p.val * b * p.val) = p.val * b * p.val := by
    simp only [← mul_assoc, p.property.isIdempotentElem.eq]
  have hr : (p.val * b * p.val) * p.val = p.val * b * p.val := by
    rw [mul_assoc (p.val * b) p.val p.val, p.property.isIdempotentElem.eq]
  rw [← hproduct a b, ← hproduct b a, hz, smul_mul_assoc, mul_smul_comm, hl, hr]

variable [TopologicalSpace.SeparableSpace H]

theorem regularCore_not_factor_of_minimal_projection
    (p : AlgebraProjection M) (hp : IsMinimalProjectionIn M p) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U) : ¬ ScalarCenter (regularCoreAlgebra U hU M) :=
  regularCore_not_factor_of_tracial_corner p hp.1 Ω hsep hcyc
    (minimal_corner_vector_tracial p hp Ω) U hU hn hm

theorem regularCore_not_factor_of_typeI (hM : IsTypeIFactor M) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U) : ¬ ScalarCenter (regularCoreAlgebra U hU M) := by
  obtain ⟨p, hp⟩ := hM.minimal
  exact regularCore_not_factor_of_minimal_projection p hp Ω hsep hcyc U hU hn hm

end

end KadisonKastler

end OAI
