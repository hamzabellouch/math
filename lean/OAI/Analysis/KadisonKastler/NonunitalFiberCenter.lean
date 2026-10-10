import OAI.Analysis.KadisonKastler.FixedFiberFactors
import OAI.Analysis.KadisonKastler.UnitizedCommonFields

namespace OAI

/-! # Scalar centers of nonunital representation ranges

These adapters keep the range Hilbert space and its unit projection inside
one definition when a common source is restricted to a smaller algebra.
-/

namespace KadisonKastler

open KadisonSimilarity
open scoped lp

noncomputable section

variable {X A B C K : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def NonunitalFiberScalarCenter (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) : Prop :=
  ∀ a : (representationVonNeumannAlgebra (nonunitalRangeRepresentation ρ)).toStarSubalgebra,
    (∀ c, a * c = c * a) → ∃ z : ℂ, a = algebraMap ℂ _ z

theorem nonunitalFiberScalarCenter_restrict_starLift
    (ρ : X → B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (ι : A →⋆ₐ[ℂ] B) (x : X)
    (h : NonunitalFiberScalarCenter (zeroExtendNonunitalRepresentation Set.univ
      (fun y => unitizationRestrict ι (Unitization.starLift (ρ y.val))) x)) :
    NonunitalFiberScalarCenter ((ρ x).comp ι.toNonUnitalStarAlgHom) := by
  rwa [zeroExtend_restrict_starLift_univ] at h

theorem nonunitalFiberScalarCenter_restrict_comp
    (ρ : X → C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (φ : B →⋆ₐ[ℂ] C) (ι : A →⋆ₐ[ℂ] B) (x : X)
    (h : NonunitalFiberScalarCenter (zeroExtendNonunitalRepresentation Set.univ
      (fun y => unitizationRestrict ι
        (Unitization.starLift ((ρ y.val).comp φ.toNonUnitalStarAlgHom))) x)) :
    NonunitalFiberScalarCenter ((ρ x).comp (φ.comp ι).toNonUnitalStarAlgHom) := by
  exact nonunitalFiberScalarCenter_restrict_starLift
    (fun y => (ρ y).comp φ.toNonUnitalStarAlgHom) ι x h

theorem fixedFiber_scalarCenter_of_nonunital
    (ρ : X → B →⋆ₙₐ[ℂ] (K →L[ℂ] K))
    (b : ℕ → K) (hb : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
    (ι : A →⋆ₐ[ℂ] B) (n : ℕ)
    (x : projectionRankStratum (representationUnitProjection ρ) b n)
    (h : NonunitalFiberScalarCenter ((ρ x.val).comp ι.toNonUnitalStarAlgHom)) :
    ScalarCenter (generatedVonNeumannAlgebra ((fixedFiberRepresentation ρ b hb n x).comp ι).range) :=
  fixedFiber_scalarCenter_of_range ρ b hb ι n x h

end

end KadisonKastler

end OAI
