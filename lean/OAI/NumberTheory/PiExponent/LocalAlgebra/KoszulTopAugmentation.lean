import OAI.NumberTheory.PiExponent.Jets.KoszulTopDifferential
import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceAugmentation

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R A B C : Type*} [CommRing R]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module R A] [Module R B] [Module R C]

lemma range_comp_eq_of_surjective (f : B →ₗ[R] C) (g : A →ₗ[R] B)
    (hg : Function.Surjective g) : LinearMap.range (f.comp g) = LinearMap.range f := by
  ext c
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨g a, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hg b
    exact ⟨a, rfl⟩

theorem scalar_sub_range (e : A ≃ₗ[R] R) (g : B →ₗ[R] R) (r : R)
    (I : Ideal R) (hg : LinearMap.range g = I) :
    LinearMap.range
      (r • e.toLinearMap.comp (LinearMap.fst R A B) -
        g.comp (LinearMap.snd R A B)) = I ⊔ Ideal.span {r} := by
  let T : (A × B) →ₗ[R] (B × R) :=
    (-(LinearMap.snd R A B)).prod (e.toLinearMap.comp (LinearMap.fst R A B))
  have hT : Function.Surjective T := by
    rintro ⟨b, z⟩
    refine ⟨(e.symm z, -b), ?_⟩
    change (-(-b), e (e.symm z)) = (b, z)
    simp only [neg_neg, e.apply_symm_apply]
  have hmap : r • e.toLinearMap.comp (LinearMap.fst R A B) -
      g.comp (LinearMap.snd R A B) = (coneBottom g r).comp T := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change r • e a - g b = g (-b) + r • e a
    rw [map_neg]
    abel
  rw [hmap, range_comp_eq_of_surjective _ _ hT, coneBottom_range_eq_sup g r I hg]

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_top_dual_image
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S) (n : ℕ)
    (hbound : ∀ k, n + 1 < k → Subsingleton (P.X k))
    (e : P.X (n + 1) ≃ₗ[S] S) (I : Ideal S)
    (hI : LinearMap.range
      ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap) = I) :
    LinearMap.range
      ((W31.scalarConeTopDualCoordinate P r (n + 1) hbound e).toLinearMap.comp
        ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap) =
      I ⊔ Ideal.span {r} := by
  let E := dualProdDualEquivDual S (P.X (n + 1)) (P.X n)
  let F := (W31.scalarConeTopDualCoordinate P r (n + 1) hbound e).toLinearMap.comp
    ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap
  have hmap : F.comp E.toLinearMap =
      r • (W31.topDualCoordinate e).toLinearMap.comp
          (LinearMap.fst S (Dual S (P.X (n + 1))) (Dual S (P.X n))) -
        ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap).comp
          (LinearMap.snd S (Dual S (P.X (n + 1))) (Dual S (P.X n))) := by
    apply LinearMap.ext
    rintro ⟨α, β⟩
    exact W31.scalarConeTopDualCoordinate_boundary P r n hbound e α β
  change LinearMap.range F = _
  rw [← range_comp_eq_of_surjective F E.toLinearMap E.surjective, hmap]
  exact scalar_sub_range (W31.topDualCoordinate e) _ r I hI

end PiExponentSiegelAux.W30

end OAI
