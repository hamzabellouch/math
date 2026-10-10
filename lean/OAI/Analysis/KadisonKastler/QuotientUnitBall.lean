import OAI.Analysis.KadisonKastler.SpectralClipping
import OAI.Analysis.Pureness.Completion.ClosedStarIdealQuotientCStar
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.RingTheory.Congruence.Hom

namespace OAI

/-! # Closed star-homomorphism ranges and contractive lifts

The closed-range assertion uses the actual C-star quotient by the kernel.
Clipping a preimage then gives an exact contraction lift, including at the
boundary of the closed unit ball. No faithfulness assumption is needed.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

local instance quotientUnitBallOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance quotientUnitBallStarOrder : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

private def starHomClosedKernel (φ : A →⋆ₐ[ℂ] B) : CuntzPureness.ClosedStarIdeal A where
  ideal := TwoSidedIdeal.ofRingCon (RingCon.ker φ.toAlgHom.toRingHom)
  star_mem {x} hx := by
    change φ (star x) = φ 0
    change φ x = φ 0 at hx
    simpa only [map_star, map_zero, star_zero] using congrArg star hx
  isClosed := by
    change IsClosed {x : A | φ x = φ 0}
    have hc : Continuous φ :=
      (φ.toAlgHom.toLinearMap.mkContinuous 1 (fun x => by
        change ‖φ x‖ ≤ 1 * ‖x‖
        simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ x)).continuous
    exact isClosed_eq hc continuous_const

private def starHomKernelQuotient (φ : A →⋆ₐ[ℂ] B) :
    (starHomClosedKernel φ).Quotient →⋆ₐ[ℂ] B :=
  { RingCon.kerLiftₐ φ.toAlgHom with
    map_star' q := by
      obtain ⟨x, rfl⟩ := (starHomClosedKernel φ).quotientMap_surjective q
      change φ (star x) = star (φ x)
      exact map_star φ x }

private theorem starHomKernelQuotient_injective (φ : A →⋆ₐ[ℂ] B) :
    Function.Injective (starHomKernelQuotient φ) :=
  RingCon.kerLiftₐ_injective φ.toAlgHom

private theorem starHomKernelQuotient_apply (φ : A →⋆ₐ[ℂ] B) (x : A) :
    starHomKernelQuotient φ ((starHomClosedKernel φ).quotientMap x) = φ x := rfl

/-- The image of a homomorphism of complete C-star algebras is norm closed. -/
theorem isClosed_starAlgHom_range (φ : A →⋆ₐ[ℂ] B) : IsClosed (Set.range φ) := by
  have hc := (NonUnitalStarAlgHom.isometry (starHomKernelQuotient φ)
    (starHomKernelQuotient_injective φ)).isClosedEmbedding.isClosed_range
  have heq : Set.range (starHomKernelQuotient φ) = Set.range φ := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := (starHomClosedKernel φ).quotientMap_surjective q
      exact ⟨x, (starHomKernelQuotient_apply φ x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨(starHomClosedKernel φ).quotientMap x, starHomKernelQuotient_apply φ x⟩
  rwa [heq] at hc

/-- Every contraction in a star-homomorphism range has a contraction preimage. -/
theorem exists_contractive_starAlgHom_preimage (φ : A →⋆ₐ[ℂ] B)
    {y : B} (hy : y ∈ Set.range φ) (hn : ‖y‖ ≤ 1) :
    ∃ x : A, ‖x‖ ≤ 1 ∧ φ x = y := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  obtain ⟨x, rfl⟩ := hy
  exact ⟨spectralClip 1 x, spectralClip_norm_le zero_lt_one x,
    map_spectralClip_eq φ zero_lt_one x hn⟩

/-- Exact image equality for closed unit balls; in particular no radius
enlargement is lost on restriction to a reducing subspace. -/
theorem image_unitBall_starAlgHom (φ : A →⋆ₐ[ℂ] B) :
    φ '' {x : A | ‖x‖ ≤ 1} = {y : B | y ∈ Set.range φ ∧ ‖y‖ ≤ 1} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, (NonUnitalStarAlgHom.norm_apply_le φ x).trans hx⟩
  · rintro ⟨hy, hn⟩
    obtain ⟨x, hx, hxy⟩ := exists_contractive_starAlgHom_preimage φ hy hn
    exact ⟨x, hx, hxy⟩

theorem isClosed_image_unitBall_starAlgHom (φ : A →⋆ₐ[ℂ] B) :
    IsClosed (φ '' {x : A | ‖x‖ ≤ 1}) := by
  rw [image_unitBall_starAlgHom]
  exact (isClosed_starAlgHom_range φ).inter
    (isClosed_le continuous_norm continuous_const)

end

end KadisonKastler

end OAI
