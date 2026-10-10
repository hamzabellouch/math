import Mathlib
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.FiniteStalkSum
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.ClosedStalk

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {K : Type} [Field K] {X Y : Scheme}

def structuralStalkMap (g : X ⟶ Spec (CommRingCat.of K)) (f : Y ⟶ X) (y : Y) :
    let _ := structuralStalkAlgebra g (f y)
    let _ := structuralStalkAlgebra (f ≫ g) y
    (X.presheaf.stalk (f y)) →ₐ[K] (Y.presheaf.stalk y) := by
  dsimp only
  letI := structuralStalkAlgebra g (f y)
  letI := structuralStalkAlgebra (f ≫ g) y
  refine { (f.stalkMap y).hom with commutes' := ?_ }
  intro scalar
  have image_mem : f y ∈ (⊤ : X.Opens) := trivial
  have point_mem : y ∈ (⊤ : Y.Opens) := trivial
  change f.stalkMap y (X.presheaf.germ ⊤ (f y) image_mem
    (g.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv scalar))) =
    Y.presheaf.germ ⊤ y point_mem
      ((f ≫ g).appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv scalar))
  rw [Scheme.Hom.comp_appTop, f.germ_stalkMap_apply]
  rfl

def closedStalkQuotientEquiv (g : X ⟶ Spec (CommRingCat.of K))
    (f : Y ⟶ X) [IsClosedImmersion f] (U : X.affineOpens) (y : Y) (hy : f y ∈ U.1) :
    let _ := structuralStalkAlgebra g (f y)
    let _ := structuralStalkAlgebra (f ≫ g) y
    ((X.presheaf.stalk (f y)) ⧸
      ((f.ker.ideal U).map (X.presheaf.germ U.1 (f y) hy).hom)) ≃ₐ[K]
      (Y.presheaf.stalk y) := by
  dsimp only
  letI := structuralStalkAlgebra g (f y)
  letI := structuralStalkAlgebra (f ≫ g) y
  have kernel_eq : RingHom.ker (structuralStalkMap g f y) =
      (f.ker.ideal U).map (X.presheaf.germ U.1 (f y) hy).hom := by
    change RingHom.ker (f.stalkMap y).hom = _
    exact closedImmersion_stalk_kernel f U y hy
  exact (Ideal.quotientEquivAlgOfEq K kernel_eq.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := structuralStalkMap g f y)
      (by
        change Function.Surjective (f.stalkMap y)
        exact f.stalkMap_surjective y))

theorem closed_local_colength_le (g : X ⟶ Spec (CommRingCat.of K))
    (f : Y ⟶ X) [IsClosedImmersion f] [IsProper (f ≫ g)] [Finite Y]
    (U : X.affineOpens) (y : Y) (hy : f y ∈ U.1) :
    let _ := structuralStalkAlgebra g (f y)
    let _ : Algebra K Γ(Y,⊤) :=
      ((f ≫ g).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    Module.finrank K ((X.presheaf.stalk (f y)) ⧸
      ((f.ker.ideal U).map (X.presheaf.germ U.1 (f y) hy).hom)) ≤
      Module.finrank K Γ(Y,⊤) := by
  dsimp only
  let := structuralStalkAlgebra g (f y)
  let := structuralStalkAlgebra (f ≫ g) y
  let : Algebra K Γ(Y,⊤) :=
    ((f ≫ g).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  rw [(closedStalkQuotientEquiv g f U y hy).toLinearEquiv.finrank_eq]
  exact (proper_finite_stalk_finrank_le (f ≫ g) y).2

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
