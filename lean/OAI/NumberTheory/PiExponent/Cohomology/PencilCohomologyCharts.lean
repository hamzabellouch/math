import OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry.BaseSections

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

def Sections (_k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) := OpenSections M U
instance (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    AddCommGroup (Sections k M U) := inferInstanceAs (AddCommGroup (OpenSections M U))
instance globalModule (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module Γ(X,⊤) (Sections k M U) := inferInstanceAs (Module Γ(X,⊤) (OpenSections M U))
instance baseModule (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module K (Sections k M U) := Module.compHom (OpenSections M U) k

def res (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    Sections k M V →ₗ[K] Sections k M U where
  toFun := openRestriction M h
  map_add' := map_add _
  map_smul' r m := (openRestriction M h).map_smul (k r) m

def congr (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U = V) :
    Sections k M U ≃ₗ[K] Sections k M V := by
  subst V
  exact LinearEquiv.refl K _

lemma congr_res (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U = V)
    (m : Sections k M ⊤) : congr k M h (res k M (show U ≤ ⊤ from le_top) m) = res k M (show V ≤ ⊤ from le_top) m := by
  subst V
  rfl

lemma congr_naturality (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U V U' V' : X.Opens} (eU : U = U') (eV : V = V')
    (h : U ≤ V) (h' : U' ≤ V') (m : Sections k M V) :
    congr k M eU (res k M h m) = res k M h' (congr k M eV m) := by
  subst U' V'
  rfl

def restrictEquiv (k : K →+* Γ(X,⊤)) (M : X.Modules)
    (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens) :
    Sections (f.appTop.hom.comp k) (M.restrict f) U ≃ₗ[K]
      Sections k M (f ''ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' r m := (restrictedOpenSections M f U).map_smul (k r) m

lemma restrictEquiv_res (k : K →+* Γ(X,⊤)) (M : X.Modules)
    (f : Y ⟶ X) [IsOpenImmersion f] {U V : Y.Opens} (h : U ≤ V)
    (m : Sections (f.appTop.hom.comp k) (M.restrict f) V) :
    restrictEquiv k M f U (res _ _ h m) =
      res k M (f.image_mono h) (restrictEquiv k M f V m) := rfl

lemma chart_image_top (U : X.Opens) : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]

lemma chart_image_preimage (U V : X.Opens) : U.ι ''ᵁ U.ι ⁻¹ᵁ V = U ⊓ V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

def chartTop (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤ ≃ₗ[K] Sections k M U :=
  (restrictEquiv k M U.ι ⊤).trans (congr k M (chart_image_top U))

def chartOverlap (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens) :
    Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) (U.ι ⁻¹ᵁ V) ≃ₗ[K]
      Sections k M (U ⊓ V) :=
  (restrictEquiv k M U.ι (U.ι ⁻¹ᵁ V)).trans
    (congr k M (chart_image_preimage U V))

lemma chartRestriction (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens)
    (m : Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤) :
    chartOverlap k M U V (res _ _ le_top m) =
      res k M (show U ⊓ V ≤ U from inf_le_left) (chartTop k M U m) := by
  change congr k M (chart_image_preimage U V)
    (restrictEquiv k M U.ι (U.ι ⁻¹ᵁ V) (res _ _ le_top m)) = _
  rw [restrictEquiv_res]
  exact congr_naturality k M (chart_image_preimage U V) (chart_image_top U)
    _ _ _

end

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
  exact { toFun := openRestriction M h
          map_add' := map_add _
          map_smul' := fun r m => (openRestriction M h).map_smul _ m }

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

end PiExponentSeshadri.Geometry.BaseSections

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

def chartModuleEquiv (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {N : Y.Modules} (e : M.restrict f ≅ N) :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    OpenSections (M.restrict f) ⊤ ≃ₗ[Γ(X,⊤)] OpenSections N ⊤ := by
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let E := moduleIsoSections e ⊤
  exact { E.toEquiv with
    map_add' := E.map_add
    map_smul' := fun r m => E.map_smul (f.appTop r) m }

def chartModuleMap (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {N : Y.Modules} (e : M.restrict f ≅ N) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    OpenSections M ⊤ →ₗ[Γ(X,⊤)] OpenSections N ⊤ := by
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  exact (chartModuleEquiv M f e).toLinearMap ∘ₗ openImmersionTop M f

theorem chartModuleMap_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] {N : Y.Modules} (e : M.restrict f ≅ N)
    (t : Γ(X,⊤)) (ht : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    IsLocalizedModule.Away t (chartModuleMap M f e) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let : IsLocalizedModule.Away t (openImmersionTop M f) :=
    openImmersionTop_localize M f t ht
  exact IsLocalizedModule.of_linearEquiv (.powers t) (openImmersionTop M f)
    (chartModuleEquiv M f e)

namespace BaseSections
variable {K : Type} [CommRing K]

def chartMap (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N) :
    Sections kX M ⊤ →ₗ[K] Sections kY N ⊤ := by
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  refine { toFun := chartModuleMap M f e
           map_add' := (chartModuleMap M f e).map_add
           map_smul' := ?_ }
  intro r m
  have h := (chartModuleMap M f e).map_smul (kX r) m
  change _ = (f.appTop (kX r)) • (chartModuleMap M f e m) at h
  exact h.trans (congrArg (fun c : Γ(Y,⊤) => c • chartModuleMap M f e m)
    (RingHom.congr_fun hk r))

lemma chartMap_smul (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N)
    (r : Γ(X,⊤)) (m : Sections kX M ⊤) :
    chartMap kX kY f hk M e (r • m) = f.appTop r • chartMap kX kY f hk M e m := by
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  exact (chartModuleMap M f e).map_smul r m

end BaseSections
end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.Geometry.BaseSections
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
end PiExponentSeshadri.Geometry.BaseSections

end

end OAI
