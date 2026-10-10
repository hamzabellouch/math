import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.AffineLocalizing
import OAI.AlgebraicGeometry.Seshadri.Divisors.BaseSections

namespace OAI

section
noncomputable section
                                            
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

variable {K : Type} [CommRing K] {X : Scheme.{0}}

@[instance_reducible]
def polynomialModule (k : K →+* Γ(X,⊤)) (t : Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module K[X] (Sections k M U) :=
  Module.compHom (Sections k M U) (Polynomial.eval₂RingHom k t)

theorem polynomialTower (k : K →+* Γ(X,⊤)) (t : Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    letI := polynomialModule k t M U
    IsScalarTower K K[X] (Sections k M U) := by
  let := polynomialModule k t M U
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change (Polynomial.eval₂RingHom k t) (Polynomial.C r) • (m : OpenSections M U) =
    k r • (m : OpenSections M U)
  simp

def polynomialRes (k : K →+* Γ(X,⊤)) (t : Γ(X,⊤)) (M : X.Modules)
    {U V : X.Opens} (h : U ≤ V) :
    letI := polynomialModule k t M U
    letI := polynomialModule k t M V
    Sections k M V →ₗ[K[X]] Sections k M U := by
  letI := polynomialModule k t M U
  letI := polynomialModule k t M V
  exact {
    toFun := openRestriction M h
    map_add' := map_add _
    map_smul' := fun polynomial sectionValue =>
      (openRestriction M h).map_smul ((Polynomial.eval₂RingHom k t) polynomial) sectionValue }

theorem polynomial_localization [IsAffine X] (k : K →+* Γ(X,⊤))
    (t : Γ(X,⊤)) (M : X.Modules) [M.IsQuasicoherent] :
    letI := polynomialModule k t M ⊤
    letI := polynomialModule k t M (X.basicOpen t)
    IsLocalizedModule.Away (Polynomial.X : K[X])
      (polynomialRes k t M (X.basicOpen_le t)) := by
  let e := Polynomial.eval₂RingHom k t
  let : Algebra K[X] Γ(X,⊤) := e.toAlgebra
  let := polynomialModule k t M ⊤
  let := polynomialModule k t M (X.basicOpen t)
  let : IsScalarTower K[X] Γ(X,⊤) (Sections k M ⊤) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower K[X] Γ(X,⊤) (Sections k M (X.basicOpen t)) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let f : Sections k M ⊤ →ₗ[Γ(X,⊤)] Sections k M (X.basicOpen t) :=
    openRestriction M (X.basicOpen_le t)
  have he : algebraMap K[X] Γ(X,⊤) Polynomial.X = t := by
    change (Polynomial.eval₂RingHom k t) Polynomial.X = t
    simp
  let : IsLocalizedModule (.powers (algebraMap K[X] Γ(X,⊤) Polynomial.X)) f := by
    rw [he]
    exact affine_openRestriction_localize M t
  exact IsLocalizedModule.restrictScalars_powers (Polynomial.X : K[X]) f

theorem polynomial_finite [IsAffine X] (k : K →+* Γ(X,⊤))
    (t : Γ(X,⊤)) (L : LineBundle X)
    (h : (Polynomial.eval₂RingHom k t).Finite) :
    letI := polynomialModule k t L.sheaf ⊤
    Module.Finite K[X] (Sections k L.sheaf ⊤) := by
  let : Algebra K[X] Γ(X,⊤) := (Polynomial.eval₂RingHom k t).toAlgebra
  let : Module.Finite K[X] Γ(X,⊤) := h
  let := polynomialModule k t L.sheaf ⊤
  let : Module.Finite Γ(X,⊤) (Sections k L.sheaf ⊤) := L.affine_openSections_finite
  let : IsScalarTower K[X] Γ(X,⊤) (Sections k L.sheaf ⊤) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  exact Module.Finite.trans Γ(X,⊤) (Sections k L.sheaf ⊤)

end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
