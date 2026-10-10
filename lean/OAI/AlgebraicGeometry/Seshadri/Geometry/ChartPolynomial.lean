import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.PolynomialSections
import OAI.AlgebraicGeometry.Seshadri.Sheaves.ChartModuleMap

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

lemma eval_transport (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) (hk : f.appTop.hom.comp kX = kY) (t : Γ(X,⊤))
    (p : K[X]) : f.appTop ((Polynomial.eval₂RingHom kX t) p) =
      (Polynomial.eval₂RingHom kY (f.appTop t)) p := by
  have h : f.appTop.hom.comp (Polynomial.eval₂RingHom kX t) =
      Polynomial.eval₂RingHom kY (f.appTop t) := by
    apply Polynomial.ringHom_ext
    · intro r
      simpa using RingHom.congr_fun hk r
    · simp
  exact RingHom.congr_fun h p

def chartPolynomialMap (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N) (t : Γ(X,⊤)) :
    letI := polynomialModule kX t M ⊤
    letI := polynomialModule kY (f.appTop t) N ⊤
    Sections kX M ⊤ →ₗ[K[X]] Sections kY N ⊤ := by
  letI := polynomialModule kX t M ⊤
  letI := polynomialModule kY (f.appTop t) N ⊤
  refine { toFun := chartMap kX kY f hk M e
           map_add' := (chartMap kX kY f hk M e).map_add
           map_smul' := ?_ }
  intro p m
  change chartMap kX kY f hk M e ((Polynomial.eval₂RingHom kX t) p • m) =
    (Polynomial.eval₂RingHom kY (f.appTop t)) p • chartMap kX kY f hk M e m
  rw [chartMap_smul, eval_transport kX kY f hk]

theorem chartPolynomialMap_localize [IsAffine X]
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) [M.IsQuasicoherent] {N : Y.Modules} (e : M.restrict f ≅ N)
    (t : Γ(X,⊤)) (ht : f.opensRange = X.basicOpen t) :
    letI := polynomialModule kX t M ⊤
    letI := polynomialModule kY (f.appTop t) N ⊤
    IsLocalizedModule.Away (Polynomial.X : K[X])
      (chartPolynomialMap kX kY f hk M e t) := by
  let : Algebra K[X] Γ(X,⊤) := (Polynomial.eval₂RingHom kX t).toAlgebra
  let := polynomialModule kX t M ⊤
  let := polynomialModule kY (f.appTop t) N ⊤
  let : Module Γ(X,⊤) (Sections kY N ⊤) :=
    Module.compHom (OpenSections N ⊤) f.appTop.hom
  let : IsScalarTower K[X] Γ(X,⊤) (Sections kX M ⊤) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower K[X] Γ(X,⊤) (Sections kY N ⊤) :=
    .of_algebraMap_smul (fun p m => by
      change f.appTop ((Polynomial.eval₂RingHom kX t) p) • (m : OpenSections N ⊤) =
        (Polynomial.eval₂RingHom kY (f.appTop t)) p • (m : OpenSections N ⊤)
      rw [eval_transport kX kY f hk])
  let F : Sections kX M ⊤ →ₗ[Γ(X,⊤)] Sections kY N ⊤ := chartModuleMap M f e
  have he : algebraMap K[X] Γ(X,⊤) Polynomial.X = t := by
    change (Polynomial.eval₂RingHom kX t) Polynomial.X = t
    simp
  let : IsLocalizedModule (.powers (algebraMap K[X] Γ(X,⊤) Polynomial.X)) F := by
    rw [he]
    exact chartModuleMap_localize M f e t ht
  have h := IsLocalizedModule.restrictScalars_powers (Polynomial.X : K[X]) F
  exact h
end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
