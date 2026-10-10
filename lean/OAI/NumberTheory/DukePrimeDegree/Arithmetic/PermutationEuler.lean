import OAI.NumberTheory.DukePrimeDegree.Geometry.SpectralMoments
import OAI.NumberTheory.DukePrimeDegree.Dynamics.SubgroupInduction

namespace OAI

/-!
# Permutation characters and local Euler determinants

The permutation representation on the group algebra and the translation
operator on functions have conjugate matrices. This connects the cyclic
induction identities to the actual Frobenius Euler determinants.
-/

noncomputable section
open scoped BigOperators Classical

namespace DukePrimeDegree

def permutationFunctionEquiv (X : Type*) [Finite X] :
    MonoidAlgebra ℂ X ≃ₗ[ℂ] (X → ℂ) :=
  (MonoidAlgebra.coeffLinearEquiv ℂ).trans (Finsupp.linearEquivFunOnFinite ℂ ℂ X)

theorem permutationFunctionEquiv_translate
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (g : G) (f : MonoidAlgebra ℂ X) :
    permutationFunctionEquiv X (Representation.ofMulAction ℂ G X g f) =
      LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g⁻¹)
        (permutationFunctionEquiv X f) := by
  funext x
  exact Representation.coeff_ofMulAction g f x

theorem permutation_euler_det_eq
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (g : G) (z : ℂ) :
    (LinearMap.id - z • Representation.ofMulAction ℂ G X g).det =
      (LinearMap.id - z •
        (LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm (β := X) g⁻¹)).toLinearMap).det := by
  let e := permutationFunctionEquiv X
  rw [← LinearMap.det_conj (LinearMap.id - z • Representation.ofMulAction ℂ G X g) e]
  congr 1
  apply LinearMap.ext
  intro f
  funext x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.smul_apply, LinearEquiv.coe_coe, map_sub, map_smul,
    LinearEquiv.apply_symm_apply]
  rw [show e (Representation.ofMulAction ℂ G X g (e.symm f)) =
    LinearEquiv.funCongrLeft ℂ ℂ (MulAction.toPerm g⁻¹) (e (e.symm f)) from
      permutationFunctionEquiv_translate g (e.symm f)]
  rw [LinearEquiv.apply_symm_apply]

theorem euler_det_products_eq_of_integer_characters
    {I G : Type*} [Fintype I] [Group G] [Finite G]
    {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, Module.Finite ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) (c : I → ℤ)
    (h : ∀ g, (∑ i, (c i : ℂ) * (ρ i).character g) = 0)
    (g : G) (z : ℂ) :
    (∏ i, (LinearMap.id - z • ρ i g).det ^ (c i).toNat) =
      ∏ i, (LinearMap.id - z • ρ i g).det ^ (-c i).toNat := by
  apply euler_det_products_eq_of_characters ρ (fun i => (c i).toNat)
    (fun i => (-c i).toNat) _ g z
  intro g
  have hc (i : I) : (c i : ℂ) = ((c i).toNat : ℂ) - ((-c i).toNat : ℂ) := by
    have := Int.toNat_sub_toNat_neg (c i)
    exact_mod_cast this.symm
  have H := h g
  simp only [hc, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] at H
  exact H

end DukePrimeDegree

end

end OAI
