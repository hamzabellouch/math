import OAI.Analysis.KadisonSimilarity.Representation.Amplification
import Mathlib.Topology.UniformSpace.UniformEmbedding

namespace OAI

/-! # Universe transfer for the similarity theorem

Raising the source algebra and the represented Hilbert space to a common
universe changes neither the bounded homomorphism nor its similarity
problem. The proof transports the actual invertible implementing operator
through the induced star algebra equivalence of operator algebras.
-/

noncomputable section
namespace KadisonSimilarity

universe u v w

namespace SimilarityUniverseTransfer

private instance uliftStarRing {A : Type u} [Ring A] [StarRing A] :
    StarRing (ULift.{v} A) where
  star x := ⟨star x.down⟩
  star_involutive x := ULift.ext _ _ (star_star x.down)
  star_mul x y := ULift.ext _ _ (star_mul x.down y.down)
  star_add x y := ULift.ext _ _ (star_add x.down y.down)

private instance uliftStarModule {A : Type u} [Ring A] [StarRing A]
    [Module ℂ A] [StarModule ℂ A] : StarModule ℂ (ULift.{v} A) where
  star_smul c x := ULift.ext _ _ (star_smul c x.down)

private instance uliftCStarAlgebra {A : Type u} [CStarAlgebra A] :
    CStarAlgebra (ULift.{v} A) where
  norm_mul_self_le x := by
    change ‖x.down‖ * ‖x.down‖ ≤ ‖star x.down * x.down‖
    exact CStarRing.norm_mul_self_le x.down

private instance uliftInnerProductSpace {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    InnerProductSpace ℂ (ULift.{v} H) where
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (𝕜 := ℂ) x.down
  conj_inner_symm x y := inner_conj_symm x.down y.down
  add_left x y z := inner_add_left x.down y.down z.down
  smul_left x y c := inner_smul_left x.down y.down c

private def uliftStarAlgEquiv (A : Type u) [CStarAlgebra A] :
    ULift.{v} A ≃⋆ₐ[ℂ] A :=
  StarAlgEquiv.ofAlgEquiv ULift.algEquiv (fun _ => rfl)

variable {A : Type u} [CStarAlgebra A]
  {B : Type w} [CStarAlgebra B]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Transport a bounded homomorphism through an algebra equivalence and an
isometric Hilbert-space equivalence. -/
def transportBoundedHom (π : BoundedUnitalHom A H)
    (eA : B ≃⋆ₐ[ℂ] A) (heA : Continuous eA) (eH : H ≃ₗᵢ[ℂ] K) :
    BoundedUnitalHom B K :=
  ⟨eH.conjStarAlgEquiv.toAlgEquiv.toAlgHom.comp (π.1.comp eA.toAlgEquiv.toAlgHom),
    eH.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous.comp
      (π.2.comp heA)⟩

/-- The invertible similarity operator transports back along the concrete
operator star algebra equivalence. -/
theorem similarToStar_of_transport (π : BoundedUnitalHom A H)
    (eA : B ≃⋆ₐ[ℂ] A) (heA : Continuous eA) (eH : H ≃ₗᵢ[ℂ] K)
    (h : SimilarToStar B K (transportBoundedHom π eA heA eH)) :
    SimilarToStar A H π := by
  obtain ⟨S, hS⟩ := h
  let φ := eH.conjStarAlgEquiv.symm
  refine ⟨Units.map φ.toAlgEquiv.toMonoidHom S, ?_⟩
  intro a
  have hs := hS (eA.symm a)
  change (S : K →L[ℂ] K) *
      eH.conjStarAlgEquiv (π.1 (eA (star (eA.symm a)))) * (↑S⁻¹ : K →L[ℂ] K) =
    star ((S : K →L[ℂ] K) *
      eH.conjStarAlgEquiv (π.1 (eA (eA.symm a))) * (↑S⁻¹ : K →L[ℂ] K)) at hs
  rw [map_star, eA.apply_symm_apply] at hs
  change φ (S : K →L[ℂ] K) * π.1 (star a) * φ (↑S⁻¹ : K →L[ℂ] K) =
    star (φ (S : K →L[ℂ] K) * π.1 a * φ (↑S⁻¹ : K →L[ℂ] K))
  simpa only [map_mul, map_star, φ, StarAlgEquiv.symm_apply_apply] using congrArg φ hs

/-- A proof in a common larger universe gives the unrestricted two-universe
similarity theorem. No representation or analytic hypothesis is added. -/
theorem similarityTheorem_of_commonUniverse
    (h : SimilarityTheorem.{max u v, max u v}) : SimilarityTheorem.{u,v} := by
  intro A _ H _ _ _ π
  let eA : ULift.{v} A ≃⋆ₐ[ℂ] A := uliftStarAlgEquiv A
  let eH : H ≃ₗᵢ[ℂ] ULift.{u} H := (LinearIsometryEquiv.ulift ℂ H : ULift.{u} H ≃ₗᵢ[ℂ] H).symm
  have heA : Continuous eA := by
    change Continuous (ULift.down : ULift.{v} A → A)
    exact continuous_uliftDown
  exact similarToStar_of_transport π eA heA eH
    (h (ULift.{v} A) (ULift.{u} H) (transportBoundedHom π eA heA eH))

end SimilarityUniverseTransfer
end KadisonSimilarity

end

end OAI
