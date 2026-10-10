import OAI.Analysis.KadisonKastler.PinchedVectorState
import OAI.Analysis.KadisonKastler.NormalCyclicCore

namespace OAI

/-! # A faithful normal state with a prescribed tracial corner vector -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def adjustedCornerVector (p : AlgebraProjection M) (Ω η : H) : WithLp 2 (H × H) :=
  WithLp.toLp 2 (η, (1 - p.val.val) Ω)

theorem adjustedCornerVector_separating (p : AlgebraProjection M) (Ω η : H)
    (hs : Function.Injective (algebraVectorMap M Ω))
    (hη : ∀ a : Algebra M, a.val η = 0 → a * p.val = 0) :
    Function.Injective (fun a : Algebra M => pinchedRepresentation M a (adjustedCornerVector p Ω η)) := by
  intro a b hab
  apply sub_eq_zero.mp
  have h₀ : (a - b).val η = 0 := by
    have he : a.val η = b.val η := congrArg WithLp.fst hab
    exact sub_eq_zero.mpr he
  have h₁ : ((a - b) * (1 - p.val)).val Ω = 0 := by
    have he : a.val ((1 - p.val.val) Ω) = b.val ((1 - p.val.val) Ω) := congrArg WithLp.snd hab
    exact sub_eq_zero.mpr he
  have haq : (a - b) * (1 - p.val) = 0 := hs (by exact h₁)
  have hap := hη (a - b) h₀
  have he : (a - b) * (1 - p.val) = a - b := by rw [mul_sub, mul_one, hap, sub_zero]
  exact he.symm.trans haq

theorem adjustedCornerVector_coefficient (p : AlgebraProjection M) (Ω η : H)
    (hη : p.val.val η = η) (a : Algebra M) :
    inner ℂ (adjustedCornerVector p Ω η)
        (pinchedRepresentation M a (adjustedCornerVector p Ω η)) =
      inner ℂ η ((p.val * a * p.val).val η) +
        inner ℂ Ω (((1 - p.val) * a * (1 - p.val)).val Ω) := by
  change inner ℂ η (a.val η) +
    inner ℂ ((1 - p.val.val) Ω) (a.val ((1 - p.val.val) Ω)) = _
  have hfirst := projection_vector_coefficient p η a
  rw [hη] at hfirst
  have hsecond := projection_vector_coefficient
    (⟨1 - p.val, p.property.one_sub⟩ : AlgebraProjection M) Ω a
  change inner ℂ ((1 - p.val.val) Ω) (a.val ((1 - p.val.val) Ω)) =
    inner ℂ Ω (((1 - p.val) * a * (1 - p.val)).val Ω) at hsecond
  rw [hfirst, hsecond]

theorem adjustedCornerVector_centralizes (p : AlgebraProjection M) (Ω η : H)
    (hη : p.val.val η = η)
    (ht : ∀ a b : Algebra M,
      inner ℂ η ((p.val * a * p.val * b * p.val).val η) =
        inner ℂ η ((p.val * b * p.val * a * p.val).val η)) (a b : Algebra M) :
    inner ℂ (adjustedCornerVector p Ω η)
        (pinchedRepresentation M (p.val * a * p.val * b) (adjustedCornerVector p Ω η)) =
      inner ℂ (adjustedCornerVector p Ω η)
        (pinchedRepresentation M (b * (p.val * a * p.val)) (adjustedCornerVector p Ω η)) := by
  rw [adjustedCornerVector_coefficient p Ω η hη,
    adjustedCornerVector_coefficient p Ω η hη]
  have h₁ : p.val * (p.val * a * p.val * b) * p.val =
      p.val * a * p.val * b * p.val := by
    simp only [← mul_assoc, p.property.isIdempotentElem.eq]
  have h₂ : p.val * (b * (p.val * a * p.val)) * p.val =
      p.val * b * p.val * a * p.val := by
    simp only [mul_assoc, p.property.isIdempotentElem.eq]
  have h₃ : (1 - p.val) * (p.val * a * p.val * b) * (1 - p.val) = 0 := by
    simp only [← mul_assoc, p.property.one_sub_mul_self, zero_mul]
  have h₄ : (1 - p.val) * (b * (p.val * a * p.val)) * (1 - p.val) = 0 := by
    simp only [mul_assoc, p.property.mul_one_sub_self, mul_zero]
  rw [h₁, h₂, h₃, h₄, ht]

variable [TopologicalSpace.SeparableSpace H]

theorem regularCore_not_factor_of_corner_trace_vector
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (Ω η : H)
    (hs : Function.Injective (algebraVectorMap M Ω))
    (hc : DenseRange (algebraVectorMap M Ω)) (hη : p.val.val η = η)
    (hηs : ∀ a : Algebra M, a.val η = 0 → a * p.val = 0)
    (hηt : ∀ a b : Algebra M,
      inner ℂ η ((p.val * a * p.val * b * p.val).val η) =
        inner ℂ η ((p.val * b * p.val * a * p.val).val η))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U) : ¬ ScalarCenter (regularCoreAlgebra U hU M) :=
  regularCore_not_factor_of_centralizing_vector_representation
    (pinchedRepresentation M) (adjustedCornerVector p Ω η)
    (adjustedCornerVector_separating p Ω η hs hηs) pinchedRepresentation_normal
    Ω hs hc p hp (adjustedCornerVector_centralizes p Ω η hη hηt) U hU hn hm

end

end KadisonKastler

end OAI
