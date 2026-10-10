import OAI.NumberTheory.PiExponent.LocalAlgebra.ConeComplex
import OAI.NumberTheory.PiExponent.LocalAlgebra.KoszulDualCone

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R A B C A' B' C' : Type*} [CommRing R]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
variable [Module R A] [Module R B] [Module R C]
variable [Module R A'] [Module R B'] [Module R C']

theorem exact_of_equivalences (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C')
    (eA : A' ≃ₗ[R] A) (eB : B' ≃ₗ[R] B) (eC : C' ≃ₗ[R] C)
    (hf : eB.toLinearMap.comp f' = f.comp eA.toLinearMap)
    (hg : eC.toLinearMap.comp g' = g.comp eB.toLinearMap)
    (hex : LinearMap.range f' = LinearMap.ker g') :
    LinearMap.range f = LinearMap.ker g := by
  have hf_apply (a : A') : eB (f' a) = f (eA a) := LinearMap.congr_fun hf a
  have hg_apply (b : B') : eC (g' b) = g (eB b) := LinearMap.congr_fun hg b
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ := eA.surjective a
    change g (f (eA a')) = 0
    rw [← hf_apply a', ← hg_apply (f' a')]
    have hz : g' (f' a') = 0 := by
      have hm : f' a' ∈ LinearMap.range f' := ⟨a', rfl⟩
      rw [hex] at hm
      exact hm
    rw [hz, map_zero]
  · intro hb
    obtain ⟨b', rfl⟩ := eB.surjective b
    have hz : g' b' = 0 := by
      apply eC.injective
      rw [map_zero, hg_apply b']
      exact hb
    have hm : b' ∈ LinearMap.range f' := by
      rw [hex]
      exact hz
    obtain ⟨a', ha'⟩ := hm
    refine ⟨eA a', ?_⟩
    rw [← hf_apply a', ha']

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_dual_interior_exact
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S) (n : ℕ)
    (hlo : LinearMap.range (P.d (n + 1) n).hom.dualMap =
      LinearMap.ker (P.d (n + 2) (n + 1)).hom.dualMap)
    (hhi : LinearMap.range (P.d (n + 2) (n + 1)).hom.dualMap =
      LinearMap.ker (P.d (n + 3) (n + 2)).hom.dualMap) :
    LinearMap.range ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap)
    (((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap)
    (dualConeDifferential (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r)
    (dualConeDifferential (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r)
    (dualProdDualEquivDual S (P.X (n + 1)) (P.X n))
    (dualProdDualEquivDual S (P.X (n + 2)) (P.X (n + 1)))
    (dualProdDualEquivDual S (P.X (n + 3)) (P.X (n + 2)))
  · have hd : (scalarConeComplex P r).d (n + 2) (n + 1) = scalarConeMap P r (n + 1) := by
      exact ChainComplex.of_d _ _ (n + 1)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r
  · have hd : (scalarConeComplex P r).d (n + 3) (n + 2) = scalarConeMap P r (n + 2) := by
      exact ChainComplex.of_d _ _ (n + 2)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r
  · exact dualConeDifferential_exact _ _ _ r hlo hhi

end PiExponentSiegelAux.W30

end OAI
