import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Nullstellensatz

namespace OAI

/-!
# Polynomial maps induced by coordinate-ring maps

The maps in this file carry actual coordinate polynomials and satisfy polynomial
composition identities. In particular, the geometric interpretation of an algebra
equivalence below is not merely a set-theoretic bijection of complex points.
-/

noncomputable section

namespace StableCoordinate
namespace AmbientMaps

open MvPolynomial

variable {k : Type*} [CommSemiring k]
variable {σ τ υ : Type*}

/-- The point map contravariantly induced by a homomorphism of polynomial algebras. -/
def pointMap (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (x : σ → k) : τ → k :=
  fun i => aeval x (φ (X i))

/-- Pulling back a polynomial and evaluating agrees with evaluating it on the point map. -/
theorem aeval_pointMap (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (x : σ → k) (p : MvPolynomial τ k) :
    aeval (pointMap φ x) p = aeval x (φ p) := by
  have h : aeval (pointMap φ x) = (aeval x).comp φ := by
    ext i
    simp [pointMap]
  exact AlgHom.congr_fun h p

@[simp]
theorem pointMap_id (x : σ → k) :
    pointMap (AlgHom.id k (MvPolynomial σ k)) x = x := by
  funext i
  simp [pointMap]

/-- Composition is reversed, as it must be for maps of coordinate rings. -/
theorem pointMap_comp (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (ψ : MvPolynomial υ k →ₐ[k] MvPolynomial τ k) (x : σ → k) :
    pointMap (φ.comp ψ) x = pointMap ψ (pointMap φ x) := by
  funext i
  exact (aeval_pointMap φ x (ψ (X i))).symm

/-- A polynomial isomorphism, with inverse identities in the polynomial rings,
not just identities of functions on the base field. -/
structure PolynomialEquiv (k : Type*) [CommSemiring k] (σ τ : Type*) where
  forward : τ → MvPolynomial σ k
  inverse : σ → MvPolynomial τ k
  forward_inverse : ∀ i, aeval forward (inverse i) = X i
  inverse_forward : ∀ i, aeval inverse (forward i) = X i

namespace PolynomialEquiv

/-- An algebra isomorphism supplies polynomial coordinates for both directions. -/
def ofAlgEquiv (e : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k) :
    PolynomialEquiv k σ τ where
  forward i := e (X i)
  inverse i := e.symm (X i)
  forward_inverse i := by
    change aeval (e.toAlgHom ∘ X) (e.symm (X i)) = X i
    rw [← aeval_unique e.toAlgHom]
    exact e.apply_symm_apply (X i)
  inverse_forward i := by
    change aeval (e.symm.toAlgHom ∘ X) (e (X i)) = X i
    rw [← aeval_unique e.symm.toAlgHom]
    exact e.symm_apply_apply (X i)

/-- The forward polynomial map. -/
def toPointMap (e : PolynomialEquiv k σ τ) (x : σ → k) : τ → k :=
  fun i => aeval x (e.forward i)

/-- The inverse polynomial map. -/
def invPointMap (e : PolynomialEquiv k σ τ) (y : τ → k) : σ → k :=
  fun i => aeval y (e.inverse i)

@[simp]
theorem invPointMap_toPointMap (e : PolynomialEquiv k σ τ) (x : σ → k) :
    e.invPointMap (e.toPointMap x) = x := by
  funext i
  change aeval (fun j => aeval x (e.forward j)) (e.inverse i) = x i
  rw [← comp_aeval_apply e.forward (aeval x), e.forward_inverse, aeval_X]

@[simp]
theorem toPointMap_invPointMap (e : PolynomialEquiv k σ τ) (y : τ → k) :
    e.toPointMap (e.invPointMap y) = y := by
  funext i
  change aeval (fun j => aeval y (e.inverse j)) (e.forward i) = y i
  rw [← comp_aeval_apply e.inverse (aeval y), e.inverse_forward, aeval_X]

/-- The underlying point equivalence, retaining its polynomial witnesses in `e`. -/
def toEquiv (e : PolynomialEquiv k σ τ) : (σ → k) ≃ (τ → k) where
  toFun := e.toPointMap
  invFun := e.invPointMap
  left_inv := e.invPointMap_toPointMap
  right_inv := e.toPointMap_invPointMap

@[simp]
theorem ofAlgEquiv_toPointMap
    (e : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k) (x : σ → k) :
    (ofAlgEquiv e).toPointMap x = pointMap e.toAlgHom x := rfl

@[simp]
theorem ofAlgEquiv_invPointMap
    (e : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k) (y : τ → k) :
    (ofAlgEquiv e).invPointMap y = pointMap e.symm.toAlgHom y := rfl

end PolynomialEquiv

/-- An ambient algebra equivalence transports every level set by an explicitly
polynomial point equivalence. The inverse direction is the one matching pullback. -/
theorem pointMap_levelSet (e : MvPolynomial τ k ≃ₐ[k] MvPolynomial σ k)
    (p : MvPolynomial τ k) (c : k) :
    pointMap e.toAlgHom ⁻¹' {y | aeval y p = c} =
      {x | aeval x (e p) = c} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, aeval_pointMap]
  rfl

end AmbientMaps
end StableCoordinate

end

end OAI
