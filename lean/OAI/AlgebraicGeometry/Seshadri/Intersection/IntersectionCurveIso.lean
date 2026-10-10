import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.CartierModule

namespace OAI

section
noncomputable section
                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {X Y : Scheme.{0}}

lemma ideal_map_comap_closed (f : Y ⟶ X) [IsClosedImmersion f]
    (J : X.IdealSheafData) : (J.comap f).map f = J ⊔ f.ker := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]
  rw [IdealPullback.comap_ideal J f ⟨f ⁻¹ᵁ U.1,U.2.preimage f⟩ U le_rfl]
  have he : (f.appLE U.1 (f ⁻¹ᵁ U.1) le_rfl).hom = (f.app U.1).hom := by
    simp [Scheme.Hom.appLE]
  rw [he,Ideal.comap_map_of_surjective _ (f.app_surjective U.1 U.2)]
  change J.ideal U ⊔ Ideal.comap (f.app U.1).hom ⊥ = J.ideal U ⊔ f.ker.ideal U
  rw [Scheme.Hom.ker_apply]
  rfl

def intrinsicIntersectionIso (I J : X.IdealSheafData) :
    (J.comap I.subschemeι).subscheme ≅ (I ⊔ J).subscheme := by
  let Q := J.comap I.subschemeι
  have hQ : Q.map I.subschemeι = I ⊔ J := by
    rw [ideal_map_comap_closed,Scheme.IdealSheafData.ker_subschemeι,sup_comm]
  let u := Scheme.IdealSheafData.subschemeMap Q (I ⊔ J) I.subschemeι hQ.ge
  have hu : u ≫ (I ⊔ J).subschemeι = Q.subschemeι ≫ I.subschemeι :=
    Scheme.IdealSheafData.subschemeMap_subschemeι Q (I ⊔ J) I.subschemeι hQ.ge
  have hk : (Q.subschemeι ≫ I.subschemeι).ker = (I ⊔ J).subschemeι.ker := by
    rw [Scheme.Hom.ker_comp,Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι,hQ]
  letI : IsIso u := IsClosedImmersion.isIso_of_ker_eq _ _ u hu hk
  exact asIso u

@[reassoc] lemma intrinsicIntersectionIso_hom_ι (I J : X.IdealSheafData) :
    (intrinsicIntersectionIso I J).hom ≫ (I ⊔ J).subschemeι =
      (J.comap I.subschemeι).subschemeι ≫ I.subschemeι :=
  by
    have hQ : I ⊔ J ≤ (J.comap I.subschemeι).map I.subschemeι := by
      rw [ideal_map_comap_closed,Scheme.IdealSheafData.ker_subschemeι,sup_comm]
    change Scheme.IdealSheafData.subschemeMap _ _ _ hQ ≫ _ = _
    exact Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ hQ

variable {K : Type} [Field K]

def structuralGlobalMap (g : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) :
    letI : Algebra K Γ(X,⊤) :=
      (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    letI : Algebra K Γ(Y,⊤) :=
      ((f ≫ g).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    Γ(X,⊤) →ₐ[K] Γ(Y,⊤) := by
  letI : Algebra K Γ(X,⊤) :=
    (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  letI : Algebra K Γ(Y,⊤) :=
    ((f ≫ g).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  refine { f.appTop.hom with commutes' := ?_ }
  intro c
  change f.appTop (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)) =
    (f ≫ g).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)
  rw [Scheme.Hom.comp_appTop]
  rfl

lemma structuralGlobal_finrank_iso (g : X ⟶ Spec (CommRingCat.of K))
    (f : Y ⟶ X) [IsIso f] :
    letI : Algebra K Γ(X,⊤) :=
      (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    letI : Algebra K Γ(Y,⊤) :=
      ((f ≫ g).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    Module.finrank K Γ(X,⊤) = Module.finrank K Γ(Y,⊤) := by
  let : Algebra K Γ(X,⊤) :=
    (g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : Algebra K Γ(Y,⊤) :=
    ((f ≫ g).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  have : IsIso f.appTop := inferInstanceAs (IsIso (Scheme.Γ.map f.op))
  exact (AlgEquiv.ofBijective (structuralGlobalMap g f)
    (ConcreteCategory.bijective_of_isIso f.appTop)).toLinearEquiv.finrank_eq

lemma intrinsicIntersection_length (g : X ⟶ Spec (CommRingCat.of K))
    (I J : X.IdealSheafData) :
    letI : Algebra K Γ((I ⊔ J).subscheme,⊤) :=
      (((I ⊔ J).subschemeι ≫ g).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    letI : Algebra K Γ((J.comap I.subschemeι).subscheme,⊤) :=
      (((J.comap I.subschemeι).subschemeι ≫ (I.subschemeι ≫ g)).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    Module.finrank K Γ((I ⊔ J).subscheme,⊤) =
      Module.finrank K Γ((J.comap I.subschemeι).subscheme,⊤) := by
  have h := structuralGlobal_finrank_iso ((I ⊔ J).subschemeι ≫ g)
    (intrinsicIntersectionIso I J).hom
  rw [← Category.assoc,intrinsicIntersectionIso_hom_ι,Category.assoc] at h
  exact h

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
