import OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech

namespace OAI

namespace PiExponent.CurveFinitePushforwardCohomology
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Geometry.BaseSections

variable {K : Type} [Field K] {X Y : Scheme.{0}}

def sectionsEquiv (f : Y ⟶ X) (k : K →+* Γ(X,⊤)) (M : Y.Modules) (U : X.Opens) :
    Sections k ((Scheme.Modules.pushforward f).obj M) U ≃ₗ[K]
      Sections (f.appTop.hom.comp k) M (f ⁻¹ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change Γ(M,f ⁻¹ᵁ U) at m
    let : Module Γ(Y,f ⁻¹ᵁ U) Γ(M,f ⁻¹ᵁ U) := (M.val.obj (op (f ⁻¹ᵁ U))).isModule
    change f.app U (restrictScalar X U (k r)) • (m : Γ(M,f ⁻¹ᵁ U)) =
      restrictScalar Y (f ⁻¹ᵁ U) (f.appTop (k r)) • m
    congr 1
    exact CategoryTheory.congr_fun (f.naturality (homOfLE le_top).op) (k r)

lemma sectionsEquiv_image (f : Y ⟶ X) (k : K →+* Γ(X,⊤)) (M : Y.Modules)
    (U V : X.Opens) :
    (twoBaseImage k ((Scheme.Modules.pushforward f).obj M) U V).map
        (sectionsEquiv f k M (U ⊓ V)).toLinearMap =
      twoBaseImage (f.appTop.hom.comp k) M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, twoBaseImage] at hy ⊢
    obtain ⟨a, ha, b, hb, h⟩ :=
      (Submodule.mem_sup (R := K)
        (M := Sections k ((Scheme.Modules.pushforward f).obj M) (U ⊓ V))).mp hy
    exact (Submodule.mem_sup (R := K)
      (M := Sections (f.appTop.hom.comp k) M ((f ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ V)))).mpr
      ⟨a, ha, b, hb, h⟩
  · intro hx
    refine ⟨x, ?_, rfl⟩
    simp only [twoBaseImage] at hx ⊢
    obtain ⟨a, ha, b, hb, h⟩ :=
      (Submodule.mem_sup (R := K)
        (M := Sections (f.appTop.hom.comp k) M ((f ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ V)))).mp hx
    exact (Submodule.mem_sup (R := K)
      (M := Sections k ((Scheme.Modules.pushforward f).obj M) (U ⊓ V))).mpr
      ⟨a, ha, b, hb, h⟩

def cohomologyOneEquiv (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (k : K →+* Γ(X,⊤))
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) :
    letI := Module.compHom (cohomology M 1) (f.appTop.hom.comp k)
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) 1) k
    cohomology M 1 ≃ₗ[K] cohomology ((Scheme.Modules.pushforward f).obj M) 1 := by
  letI := Module.compHom (cohomology M 1) (f.appTop.hom.comp k)
  letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) 1) k
  have hpre : (f ⁻¹ᵁ U) ⊔ (f ⁻¹ᵁ V) = ⊤ := by
    change f ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover, Scheme.Hom.preimage_top]
  let eY := twoBaseCohomologyOne (f.appTop.hom.comp k) M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
    (hU.preimage f) (hV.preimage f) hpre
  let eX := twoBaseCohomologyOne k ((Scheme.Modules.pushforward f).obj M) U V hU hV hcover
  let eSections : Sections k ((Scheme.Modules.pushforward f).obj M) (U ⊓ V) ≃ₗ[K]
      Sections (f.appTop.hom.comp k) M ((f ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ V)) :=
    sectionsEquiv f k M (U ⊓ V)
  let e := Submodule.Quotient.equiv _ _ eSections (sectionsEquiv_image f k M U V)
  exact eY.symm.trans (e.symm.trans eX)

def zeroSections (k : K →+* Γ(X,⊤)) (M : X.Modules) :
    letI := Module.compHom (cohomology M 0) k
    cohomology M 0 ≃ₗ[K] Sections k M ⊤ := by
  letI := Module.compHom (cohomology M 0) k
  let e := (Ext.linearEquiv₀ (R := Γ(X,⊤)) (X := structureSheaf X) (Y := M)).trans
    (globalHomLinearEquiv M)
  refine { toFun := e
           invFun := e.symm
           left_inv := e.left_inv
           right_inv := e.right_inv
           map_add' := e.map_add
           map_smul' := ?_ }
  intro r m
  change e (k r • m) = restrictScalar X ⊤ (k r) • e m
  rw [e.map_smul]
  congr 1
  change k r = X.presheaf.map (𝟙 (op ⊤)) (k r)
  rw [X.presheaf.map_id]
  rfl

def cohomologyZeroEquiv (f : Y ⟶ X) (k : K →+* Γ(X,⊤)) (M : Y.Modules) :
    letI := Module.compHom (cohomology M 0) (f.appTop.hom.comp k)
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) 0) k
    cohomology M 0 ≃ₗ[K] cohomology ((Scheme.Modules.pushforward f).obj M) 0 := by
  letI := Module.compHom (cohomology M 0) (f.appTop.hom.comp k)
  letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) 0) k
  let e := (sectionsEquiv f k M ⊤).trans
    (BaseSections.congr (f.appTop.hom.comp k) M (Scheme.Hom.preimage_top f))
  exact (zeroSections (f.appTop.hom.comp k) M).trans
    (e.symm.trans (zeroSections k ((Scheme.Modules.pushforward f).obj M)).symm)

def cohomologyLowEquiv (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (k : K →+* Γ(X,⊤))
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (n : ℕ) (hn : n ≤ 1) :
    letI := Module.compHom (cohomology M n) (f.appTop.hom.comp k)
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) k
    cohomology M n ≃ₗ[K] cohomology ((Scheme.Modules.pushforward f).obj M) n := by
  by_cases hn0 : n = 0
  · subst n
    exact cohomologyZeroEquiv f k M
  · have hn1 : n = 1 := by omega
    subst n
    exact cohomologyOneEquiv f k M U V hU hV hcover

theorem finiteDimensional_of_pushforward (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (k : K →+* Γ(X,⊤))
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (n : ℕ) (hn : n ≤ 1)
    (hfinite : letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) k
      FiniteDimensional K (cohomology ((Scheme.Modules.pushforward f).obj M) n)) :
    let := Module.compHom (cohomology M n) (f.appTop.hom.comp k)
    FiniteDimensional K (cohomology M n) := by
  let := Module.compHom (cohomology M n) (f.appTop.hom.comp k)
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) k
  have := hfinite
  let e := cohomologyLowEquiv f k M U V hU hV hcover n hn
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

theorem finiteDimensional_pushforward (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (k : K →+* Γ(X,⊤))
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (n : ℕ) (hn : n ≤ 1)
    (hfinite : letI := Module.compHom (cohomology M n) (f.appTop.hom.comp k)
      FiniteDimensional K (cohomology M n)) :
    let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) k
    FiniteDimensional K (cohomology ((Scheme.Modules.pushforward f).obj M) n) := by
  let := Module.compHom (cohomology M n) (f.appTop.hom.comp k)
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) k
  have := hfinite
  let e := cohomologyLowEquiv f k M U V hU hV hcover n hn
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

lemma baseScalars_comp (f : Y ⟶ X) (p : X ⟶ Spec (CommRingCat.of ℂ)) :
    baseScalars (f ≫ p) = f.appTop.hom.comp (baseScalars p) := by
  ext c
  simp only [baseScalars, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

theorem cohomologyDimension_pushforward (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (n : ℕ) (hn : n ≤ 1) :
    cohomologyDimension p ((Scheme.Modules.pushforward f).obj M) n =
      cohomologyDimension (f ≫ p) M n := by
  unfold cohomologyDimension
  rw [baseScalars_comp]
  let := Module.compHom (cohomology M n) (f.appTop.hom.comp (baseScalars p))
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  exact (cohomologyLowEquiv f (baseScalars p) M U V hU hV hcover n hn).finrank_eq.symm

theorem euler_one_pushforward (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) :
    eulerCharacteristic p 1 ((Scheme.Modules.pushforward f).obj M) =
      eulerCharacteristic (f ≫ p) 1 M := by
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n ≤ 1 := by
    have h := Finset.mem_range.mp hn
    omega
  rw [cohomologyDimension_pushforward f p M U V hU hV hcover n hn']

end
end PiExponent.CurveFinitePushforwardCohomology

end OAI
