import OAI.Analysis.OperatorAlgebra.GNSBundledOperators

namespace OAI

/-! The canonical GNS representation on the explicitly bundled Hilbert space. -/
noncomputable section
open scoped ComplexOrder
namespace WeakPureInfiniteness

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def gnsBundledHom (f : A →ₚ[ℂ] ℂ) : A →⋆ₐ[ℂ] (gnsHilbert f →L[ℂ] gnsHilbert f) :=
  f.gnsStarAlgHom

lemma gnsBundledHom_apply (f : A →ₚ[ℂ] ℂ) (a : A) :
    gnsBundledHom f a = gnsBundledLeft f a := rfl

lemma gnsBundledHom_cyclic (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a => gnsBundledHom f a (gnsVector f 1)) := by
  intro x
  refine gnsVector_induction_on f x isClosed_closure ?_
  intro a
  apply subset_closure
  refine ⟨a, ?_⟩
  change gnsBundledLeft f a (gnsVector f 1) = gnsVector f a
  rw [gnsBundledLeft_vector, mul_one]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma cyclicBundledGNSIsometry_intertwines (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hf : ∀ a, f a = inner ℂ ξ (π a ξ)) (a : A) :
    (cyclicBundledGNSIsometry f π ξ hf).toContinuousLinearMap.comp (gnsBundledHom f a) =
      (π a).comp (cyclicBundledGNSIsometry f π ξ hf).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  exact cyclicGNSIsometry_intertwines f π ξ hf a x

lemma cyclicBundledGNSIsometry_one (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hf : ∀ a, f a = inner ℂ ξ (π a ξ)) :
    cyclicBundledGNSIsometry f π ξ hf (gnsVector f 1) = ξ := by
  exact (cyclicBundledGNSIsometry_vector f π ξ hf (1 : A)).trans (by
    rw [map_one]
    rfl)

end WeakPureInfiniteness

end

end OAI
