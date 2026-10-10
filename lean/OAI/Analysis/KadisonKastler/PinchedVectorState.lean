import OAI.Analysis.KadisonKastler.HilbertPairRepresentation
import OAI.Analysis.KadisonKastler.NormalCyclicRealization

namespace OAI

/-! # The faithful normal vector state obtained by pinching at a projection -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def pinchedRepresentation (M : VonNeumannAlgebra H) :
    Algebra M →⋆ₐ[ℂ] (WithLp 2 (H × H) →L[ℂ] WithLp 2 (H × H)) :=
  hilbertPairRepresentation M.toStarSubalgebra.subtype M.toStarSubalgebra.subtype

def pinchedVector (p : AlgebraProjection M) (Ω : H) : WithLp 2 (H × H) :=
  WithLp.toLp 2 (p.val.val Ω, (1 - p.val.val) Ω)

theorem pinchedRepresentation_normal : BoundedWeakNormal M (pinchedRepresentation M) := by
  intro ι l a b C ha hb x y
  change Tendsto (fun i => inner ℂ y.fst ((a i).val x.fst) +
    inner ℂ y.snd ((a i).val x.snd)) l
    (𝓝 (inner ℂ y.fst (b.val x.fst) + inner ℂ y.snd (b.val x.snd)))
  exact (hb x.fst y.fst).add (hb x.snd y.snd)

theorem pinchedVector_separating (p : AlgebraProjection M) (Ω : H)
    (hs : Function.Injective (algebraVectorMap M Ω)) :
    Function.Injective (fun a : Algebra M => pinchedRepresentation M a (pinchedVector p Ω)) := by
  intro a b hab
  apply hs
  have h₀ : a.val (p.val.val Ω) = b.val (p.val.val Ω) := congrArg WithLp.fst hab
  have h₁ : a.val ((1 - p.val.val) Ω) = b.val ((1 - p.val.val) Ω) := congrArg WithLp.snd hab
  have he : p.val.val Ω + (1 - p.val.val) Ω = Ω := by
    rw [sub_apply, one_apply_eq_self, add_sub_cancel]
  change a.val Ω = b.val Ω
  rw [← he, map_add, map_add, h₀, h₁]

theorem projection_vector_coefficient (p : AlgebraProjection M) (Ω : H) (a : Algebra M) :
    inner ℂ (p.val.val Ω) (a.val (p.val.val Ω)) =
      inner ℂ Ω ((p.val * a * p.val).val Ω) := by
  have hp : p.val.val.adjoint = p.val.val := by
    exact congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  rw [← ContinuousLinearMap.adjoint_inner_right, hp]
  rfl

theorem pinchedVector_coefficient (p : AlgebraProjection M) (Ω : H) (a : Algebra M) :
    inner ℂ (pinchedVector p Ω) (pinchedRepresentation M a (pinchedVector p Ω)) =
      inner ℂ Ω ((p.val * a * p.val + (1 - p.val) * a * (1 - p.val)).val Ω) := by
  change inner ℂ (p.val.val Ω) (a.val (p.val.val Ω)) +
    inner ℂ ((1 - p.val.val) Ω) (a.val ((1 - p.val.val) Ω)) = _
  have hc := projection_vector_coefficient
    (⟨1 - p.val, p.property.one_sub⟩ : AlgebraProjection M) Ω a
  change inner ℂ ((1 - p.val.val) Ω) (a.val ((1 - p.val.val) Ω)) =
    inner ℂ Ω (((1 - p.val) * a * (1 - p.val)).val Ω) at hc
  rw [projection_vector_coefficient p Ω a, hc]
  exact (inner_add_right _ _ _).symm

theorem pinchedVector_centralizes_corner (p : AlgebraProjection M) (Ω : H)
    (htrace : ∀ a b : Algebra M,
      inner ℂ Ω ((p.val * a * p.val * b * p.val).val Ω) =
        inner ℂ Ω ((p.val * b * p.val * a * p.val).val Ω))
    (a b : Algebra M) :
    inner ℂ (pinchedVector p Ω)
        (pinchedRepresentation M (p.val * a * p.val * b) (pinchedVector p Ω)) =
      inner ℂ (pinchedVector p Ω)
        (pinchedRepresentation M (b * (p.val * a * p.val)) (pinchedVector p Ω)) := by
  rw [pinchedVector_coefficient, pinchedVector_coefficient]
  have h₁ : p.val * (p.val * a * p.val * b) * p.val +
      (1 - p.val) * (p.val * a * p.val * b) * (1 - p.val) =
      p.val * a * p.val * b * p.val := by
    simp only [← mul_assoc, p.property.isIdempotentElem.eq,
      p.property.one_sub_mul_self, zero_mul, add_zero]
  have h₂ : p.val * (b * (p.val * a * p.val)) * p.val +
      (1 - p.val) * (b * (p.val * a * p.val)) * (1 - p.val) =
      p.val * b * p.val * a * p.val := by
    simp only [mul_assoc, p.property.isIdempotentElem.eq,
      p.property.mul_one_sub_self, mul_zero, add_zero]
  rw [h₁, h₂]
  exact htrace a b

end

end KadisonKastler

end OAI
