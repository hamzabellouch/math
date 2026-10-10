import OAI.Algebra.AuslanderReiten.Coordinates.FiniteConnectingProducts

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R] [CharP k 2]
variable (τ : FrobeniusTrace k R) (S M N L : FiniteLeftModule k R) (n : ℤ)

def HasSourceCoordinates
    (u : CohomologyClass (S.completeCochain τ) (M.completeCochain τ) n)
    (s : RawCokernelAt (S.completeCochain τ) n →ₗ[R] M.carrier) : Prop :=
  resolutionSourceAtStableEquiv τ S M n u = StableHom.classOf R _ _ s

def SourceQuotientSquare (g : N.carrier →ₗ[R] L.carrier)
    (s : RawCokernelAt (S.completeCochain τ) n →ₗ[R] L.carrier)
    (A : (S.completeCochain τ).X (-n) →ₗ[R] N.carrier) : Prop :=
  g.comp A = s.comp (LinearMap.range ((S.completeCochain τ).d (-(n+1)) (-n)).hom).mkQ

def SourceInclusionSquare (f : M.carrier →ₗ[R] N.carrier)
    (A : (S.completeCochain τ).X (-n) →ₗ[R] N.carrier)
    (t : RawCokernelAt (S.completeCochain τ) (n+1) →ₗ[R] M.carrier) : Prop :=
  f.comp t = A.comp (rawCokernelAtInclusion (S.completeCochain τ) n)

variable {S M N L n}
theorem HasSourceCoordinates.connecting_product
    (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)
    (u : CohomologyClass (S.completeCochain τ) (L.completeCochain τ) n)
    (s : RawCokernelAt (S.completeCochain τ) n →ₗ[R] L.carrier)
    (A : (S.completeCochain τ).X (-n) →ₗ[R] N.carrier)
    (t : RawCokernelAt (S.completeCochain τ) (n+1) →ₗ[R] M.carrier)
    (hs : HasSourceCoordinates τ S L n u s)
    (hA : SourceQuotientSquare τ S N L n g s A)
    (ht : SourceInclusionSquare τ S M N n f A t) :
    HasSourceCoordinates τ S M (n+1)
      (fullHomProduct u ((fullHomShiftedHomotopyEquiv k _ _ 1).symm
        (resolutionConnecting τ f g hf hg hex))) t :=
  resolutionConnecting_product_source τ f g hf hg hex n u s hs A t hA ht

end ArExplicit.FiniteLeftModule

end

end OAI
