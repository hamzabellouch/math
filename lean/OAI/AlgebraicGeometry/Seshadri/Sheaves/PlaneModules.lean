import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.ChartModuleMap
import OAI.AlgebraicGeometry.Seshadri.Geometry.PlaneChartAlgebra

namespace OAI


                                      
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.LaurentPlane

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

@[instance_reducible]
def laurentModule (k : K →+* Γ(Y,⊤)) (u v : Γ(Y,⊤)ˣ) (N : Y.Modules) :
    Module (LaurentPlane.Ring K) (Sections k N ⊤) :=
  Module.compHom (Sections k N ⊤) (LaurentPlane.eval k u v)

theorem laurentTower (k : K →+* Γ(Y,⊤)) (u v : Γ(Y,⊤)ˣ) (N : Y.Modules) :
    letI := laurentModule k u v N
    IsScalarTower K (LaurentPlane.Ring K) (Sections k N ⊤) := by
  let := laurentModule k u v N
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change LaurentPlane.eval k u v (algebraMap K (LaurentPlane.Ring K) r) •
    (m : OpenSections N ⊤) = k r • (m : OpenSections N ⊤)
  rw [LaurentPlane.eval_algebraMap]

theorem chartMap_clearing [IsAffine X]
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) [M.IsQuasicoherent] {N : Y.Modules} (e : M.restrict f ≅ N)
    (a : Γ(X,⊤)) (ha : f.opensRange = X.basicOpen a) (m : Sections kY N ⊤) :
    ∃ d : ℕ, f.appTop a ^ d • m ∈ (chartMap kX kY f hk M e).range := by
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let F := chartModuleMap M f e
  let : IsLocalizedModule.Away a F := chartModuleMap_localize M f e a ha
  obtain ⟨d,n,hn⟩ := (inferInstance : IsLocalizedModule.Away a F).surj _ _ m
  refine ⟨d,n,?_⟩
  change f.appTop (a^d) • (m : OpenSections N ⊤) = F n at hn
  change F n = f.appTop a ^ d • (m : OpenSections N ⊤)
  rw [map_pow] at hn
  exact hn.symm

theorem laurent_finite_of_affine [IsAffine X] {P : Type} [CommRing P]
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (L : LineBundle X) {N : Y.Modules} (d : L.sheaf.restrict f ≅ N)
    (a b : Γ(X,⊤)) (hopen : f.opensRange = X.basicOpen (a*b))
    (u v : Γ(Y,⊤)ˣ) (hu : f.appTop a = u) (hv : f.appTop b = v)
    (p : P →+* Γ(X,⊤)) (hp : p.Finite) (e : P →+* LaurentPlane.Ring K)
    (he : f.appTop.hom.comp p = (LaurentPlane.eval kY u v).comp e) :
    letI := laurentModule kY u v N
    Module.Finite (LaurentPlane.Ring K) (Sections kY N ⊤) := by
  let := laurentModule kY u v N
  let : Algebra P Γ(X,⊤) := p.toAlgebra
  let : Module.Finite P Γ(X,⊤) := hp
  let : Module P (Sections kX L.sheaf ⊤) := Module.compHom _ p
  let : Module.Finite Γ(X,⊤) (Sections kX L.sheaf ⊤) := L.affine_openSections_finite
  let : IsScalarTower P Γ(X,⊤) (Sections kX L.sheaf ⊤) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let : Module.Finite P (Sections kX L.sheaf ⊤) := Module.Finite.trans Γ(X,⊤) _
  let F := chartMap kX kY f hk L.sheaf d
  apply LaurentPlane.finite_laurent_of_chart kY u v e F.toAddMonoidHom
  · intro q m
    change F (p q • m) = _
    rw [chartMap_smul]
    exact congrArg (fun c : Γ(Y,⊤) => c • F m) (RingHom.congr_fun he q)
  · intro m
    obtain ⟨n,z,hz⟩ := chartMap_clearing kX kY f hk L.sheaf d (a*b) hopen m
    refine ⟨n,z,?_⟩
    change (↑u * ↑v : Γ(Y,⊤))^n • m = chartMap kX kY f hk L.sheaf d z
    simpa only [map_mul,hu,hv] using hz.symm

lemma chartMap_monomial_mem
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N)
    (u v : Γ(Y,⊤)ˣ) (z : ℤ × ℤ)
    (h : ∃ a : Γ(X,⊤), f.appTop a = LaurentPlane.eval kY u v (T z)) :
    letI := laurentModule kY u v N
    ∀ m ∈ (chartMap kX kY f hk M e).range,
      T (K := K) z • m ∈ (chartMap kX kY f hk M e).range := by
  let := laurentModule kY u v N
  rintro m ⟨n,rfl⟩
  obtain ⟨a,ha⟩ := h
  refine ⟨a • n,?_⟩
  change chartMap kX kY f hk M e (a • n) =
    LaurentPlane.eval kY u v (T z) • chartMap kX kY f hk M e n
  rw [chartMap_smul,ha]

end
end MaximalSeshadri.Geometry.BaseSections

end

end OAI
