import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.SmoothAffineRefinement
import OAI.AlgebraicGeometry.Seshadri.Intersection.SchematicIntersection
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.ClosedColength

namespace OAI

section
noncomputable section
                                                  
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.ProjectiveBertini

variable {K : Type} [Field K] {X : Scheme}

lemma structuralStalkAlgebra_eq_open (g : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    structuralStalkAlgebra g x =
      ((X.presheaf.germ U x hx).hom.comp (openScalars g U)).toAlgebra := by
  apply congrArg RingHom.toAlgebra
  ext k
  change (X.presheaf.germ ⊤ x trivial) (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv k)) = _
  unfold openScalars Scheme.Hom.appLE
  change _ = (g.app ⊤ ≫ X.presheaf.map _ ≫ X.presheaf.germ U x hx) _
  rw [TopCat.Presheaf.germ_res]
  rfl

theorem intersection_local_colength_le (g : X ⟶ Spec (CommRingCat.of K)) [IsProper g]
    (I J : X.IdealSheafData) [IsIntegral I.subscheme]
    (hd : topologicalKrullDim I.subscheme ≤ 1) (hJ : ¬ J ≤ I)
    (U : X.affineOpens) (y : (I ⊔ J).subscheme)
    (hy : (I ⊔ J).subschemeι y ∈ U.1) (t f : Γ(X,U.1))
    (hI : I.ideal U = Ideal.span {t}) (hF : J.ideal U = Ideal.span {f}) :
    let _ : Algebra K (X.presheaf.stalk ((I ⊔ J).subschemeι y)) :=
      ((X.presheaf.germ U.1 ((I ⊔ J).subschemeι y) hy).hom.comp (openScalars g U.1)).toAlgebra
    let _ : Algebra K Γ((I ⊔ J).subscheme,⊤) :=
      (((I ⊔ J).subschemeι ≫ g).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    Module.finrank K ((X.presheaf.stalk ((I ⊔ J).subschemeι y)) ⧸ Ideal.span
      {X.presheaf.germ U.1 ((I ⊔ J).subschemeι y) hy f,
       X.presheaf.germ U.1 ((I ⊔ J).subschemeι y) hy t}) ≤
      Module.finrank K Γ((I ⊔ J).subscheme,⊤) := by
  let : Finite (I ⊔ J).subscheme := finite_schematic_intersection g I J hd hJ
  have h := closed_local_colength_le g (I ⊔ J).subschemeι U y hy
  rw [structuralStalkAlgebra_eq_open g U.1 _ hy] at h
  have he : (((I ⊔ J).subschemeι.ker).ideal U).map
      (X.presheaf.germ U.1 ((I ⊔ J).subschemeι y) hy).hom = Ideal.span
      {X.presheaf.germ U.1 ((I ⊔ J).subschemeι y) hy f,
       X.presheaf.germ U.1 ((I ⊔ J).subschemeι y) hy t} := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    change Ideal.map _ (I.ideal U ⊔ J.ideal U) = _
    rw [hI,hF,Ideal.map_sup,Ideal.map_span,Ideal.map_span]
    simp only [Set.image_singleton]
    rw [← Ideal.span_union]
    simp only [Set.singleton_union]
    rw [Set.pair_comm]
  rw [he] at h
  exact h

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
