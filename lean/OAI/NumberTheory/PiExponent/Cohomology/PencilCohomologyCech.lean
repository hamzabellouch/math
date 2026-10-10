import OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts
import OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyLaurent

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ExtCokernel
open CategoryTheory CategoryTheory.Abelian
universe w v u t
variable {K : Type t} [CommRing K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C] {S : ShortComplex C}

def quotientEquiv (hS : S.ShortExact) (M : C)
    (hvan : ∀ x : Ext S.X₂ M 1, x = 0) :
    ((S.X₁ ⟶ M) ⧸ (LinearMap.range
      (Linear.leftComp K M S.f))) ≃ₗ[K] Ext S.X₃ M 1 := by
  let d : (S.X₁ ⟶ M) →ₗ[K] Ext S.X₃ M 1 :=
    (hS.extClass.precompOfLinear K M (add_zero 1)).comp Ext.linearEquiv₀.symm.toLinearMap
  have hd : Function.Surjective d := by
    intro x
    obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ hS M x (hvan _) (n₀ := 0) rfl
    refine ⟨Ext.linearEquiv₀ (R := K) y, ?_⟩
    change hS.extClass.comp (Ext.mk₀ (Ext.linearEquiv₀ (R := K) y)) (add_zero 1) = x
    rwa [Ext.mk₀_linearEquiv₀_apply]
  have hk : LinearMap.range (Linear.leftComp K M S.f) = d.ker := by
    ext f
    constructor
    · rintro ⟨g,rfl⟩
      change hS.extClass.comp (Ext.mk₀ (S.f ≫ g)) (add_zero 1) = 0
      rw [← Ext.mk₀_comp_mk₀]
      exact ShortComplex.ShortExact.extClass_comp_assoc hS _
    · intro hf
      change hS.extClass.comp (Ext.mk₀ f) (add_zero 1) = 0 at hf
      obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₁ hS M (Ext.mk₀ f) rfl hf
      refine ⟨Ext.linearEquiv₀ (R := K) y, ?_⟩
      apply (Ext.linearEquiv₀ (R := K)).symm.injective
      change Ext.mk₀ (S.f ≫ Ext.linearEquiv₀ (R := K) y) = Ext.mk₀ f
      simpa only [← Ext.mk₀_comp_mk₀,
        Ext.mk₀_linearEquiv₀_apply] using hy
  exact (Submodule.quotEquivOfEq _ _ hk).trans (d.quotKerEquivOfSurjective hd)

end PiExponentSeshadri.ExtCokernel

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque
variable {X : Scheme.{0}}
local instance : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) := sheafLinear X
local instance : HasExt.{1} (SheafOfModules X.ringCatSheaf) := schemeHasExt

private abbrev schemeFreeOpen (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

private abbrev schemeShortComplex (U V : X.Opens) : ShortComplex X.Modules :=
  ModuleMayerVietoris.shortComplex X.ringCatSheaf U V

private abbrev schemeFreeOpenEquiv (M : X.Modules) (U : X.Opens) :
    (schemeFreeOpen U ⟶ M) ≃ₗ[Γ(X,⊤)] OpenSections M U :=
  freeOpenLinearEquiv M U

def twoChartImage (M : X.Modules) (U V : X.Opens) :
    Submodule Γ(X,⊤) (OpenSections M (U ⊓ V)) :=
  (openRestriction M (show U ⊓ V ≤ U from inf_le_left)).range ⊔
  (openRestriction M (show U ⊓ V ≤ V from inf_le_right)).range

lemma twoChartImage_eq (M : X.Modules) (U V : X.Opens) :
    (LinearMap.range (Linear.leftComp (C := X.Modules) (X := schemeFreeOpen (U ⊓ V))
      (Y := schemeFreeOpen U ⊞ schemeFreeOpen V) Γ(X,⊤) M
      (schemeShortComplex U V).f)).map
      (schemeFreeOpenEquiv M (U ⊓ V)).toLinearMap = twoChartImage M U V := by
  simp only [schemeShortComplex, ModuleMayerVietoris.shortComplex]
  let P := twoChartImage M U V
  let l : schemeFreeOpen (U ⊓ V) ⟶ schemeFreeOpen U :=
    freeOpenMap X.ringCatSheaf (homOfLE (show U ⊓ V ≤ U from inf_le_left))
  let r : schemeFreeOpen (U ⊓ V) ⟶ schemeFreeOpen V :=
    freeOpenMap X.ringCatSheaf (homOfLE (show U ⊓ V ≤ V from inf_le_right))
  have hl (f : schemeFreeOpen U ⟶ M) :
      schemeFreeOpenEquiv M (U ⊓ V) (l ≫ f) =
        openRestriction M inf_le_left (schemeFreeOpenEquiv M U f) :=
    freeOpenLinearEquiv_naturality M inf_le_left f
  have hr (f : schemeFreeOpen V ⟶ M) :
      schemeFreeOpenEquiv M (U ⊓ V) (r ≫ f) =
        openRestriction M inf_le_right (schemeFreeOpenEquiv M V f) :=
    freeOpenLinearEquiv_naturality M inf_le_right f
  apply le_antisymm
  · rintro x ⟨f,⟨g,rfl⟩,rfl⟩
    have he : biprod.lift l (-r) ≫ g =
        l ≫ (biprod.inl ≫ g) - r ≫ (biprod.inr ≫ g) := by
      rw [biprod.lift_eq]
      simp only [Preadditive.add_comp, Category.assoc, Preadditive.neg_comp,
        sub_eq_add_neg]
    change schemeFreeOpenEquiv M (U ⊓ V)
      (biprod.lift l (-r) ≫ g) ∈ P
    rw [he, map_sub, hl, hr]
    exact P.sub_mem
      ((show (openRestriction M inf_le_left).range ≤ P from le_sup_left)
        ((openRestriction M inf_le_left).mem_range_self _))
      ((show (openRestriction M inf_le_right).range ≤ P from le_sup_right)
        ((openRestriction M inf_le_right).mem_range_self _))
  · apply sup_le
    · rintro x ⟨a,rfl⟩
      refine ⟨_, ⟨biprod.desc ((schemeFreeOpenEquiv M U).symm a) 0,rfl⟩, ?_⟩
      change schemeFreeOpenEquiv M (U ⊓ V)
        (biprod.lift l (-r) ≫ biprod.desc ((schemeFreeOpenEquiv M U).symm a) 0) = _
      rw [biprod.lift_desc, comp_zero, add_zero, hl, LinearEquiv.apply_symm_apply]
    · rintro x ⟨b,rfl⟩
      refine ⟨_, ⟨biprod.desc 0 (-((schemeFreeOpenEquiv M V).symm b)),rfl⟩, ?_⟩
      change schemeFreeOpenEquiv M (U ⊓ V)
        (biprod.lift l (-r) ≫ biprod.desc 0 (-((schemeFreeOpenEquiv M V).symm b))) = _
      rw [biprod.lift_desc, comp_zero, zero_add, Preadditive.neg_comp,
        Preadditive.comp_neg, neg_neg, hr, LinearEquiv.apply_symm_apply]

def twoAffineUnionExtOne [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    ((OpenSections M (U ⊓ V)) ⧸ twoChartImage M U V) ≃ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) (schemeFreeOpen (U ⊔ V)) M 1 := by
  have hmid (y : Ext.{1} (C := X.Modules) (schemeFreeOpen U ⊞ schemeFreeOpen V) M 1) :
      y = 0 := by
    apply Ext.biprodAddEquiv.injective
    apply Prod.ext
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_fst, Prod.fst_zero] using
        FiniteCoverCohomology.affine_open_ext_zero U hU M 0
          ((Ext.mk₀ biprod.inl).comp y (zero_add _))
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_snd, Prod.snd_zero] using
        FiniteCoverCohomology.affine_open_ext_zero V hV M 0
          ((Ext.mk₀ biprod.inr).comp y (zero_add _))
  let e := Submodule.Quotient.equiv _ _ (schemeFreeOpenEquiv M (U ⊓ V))
    (twoChartImage_eq M U V)
  exact e.symm.trans (ExtCokernel.quotientEquiv
    (ModuleMayerVietoris.shortComplex_shortExact X.ringCatSheaf U V) M hmid)

def extSourceIso {E F : X.Modules} (e : E ≅ F) (M : X.Modules) (n : ℕ) :
    Ext.{1} (C := X.Modules) E M n ≃ₗ[Γ(X,⊤)] Ext.{1} (C := X.Modules) F M n where
  toFun := (Ext.mk₀ e.inv).precompOfLinear Γ(X,⊤) M (zero_add n)
  invFun := (Ext.mk₀ e.hom).precompOfLinear Γ(X,⊤) M (zero_add n)
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv x := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp x (zero_add n)) (zero_add n) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  right_inv x := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add n)) (zero_add n) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]

def twoAffineCohomologyOne [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hcover : U ⊔ V = ⊤) :
    ((OpenSections M (U ⊓ V)) ⧸ twoChartImage M U V) ≃ₗ[Γ(X,⊤)] cohomology M 1 := by
  let e := twoAffineUnionExtOne M U V hU hV
  rw [hcover] at e
  exact e.trans (extSourceIso (FreeOpenUnit.freeTopIso X.ringCatSheaf) M 1)

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.Geometry.BaseSections

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial
variable {K : Type} [Field K] {U V W : Scheme.{0}} [IsAffine U] [IsAffine V]

theorem two_chart_cokernel_finite
    (kU : K →+* Γ(U,⊤)) (kV : K →+* Γ(V,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ U) (b : W ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b]
    (hka : a.appTop.hom.comp kU = kW) (hkb : b.appTop.hom.comp kV = kW)
    (u : Γ(U,⊤)) (v : Γ(V,⊤))
    (ha : a.opensRange = U.basicOpen u) (hb : b.opensRange = V.basicOpen v)
    (huv : a.appTop u * b.appTop v = 1)
    (hu : (Polynomial.eval₂RingHom kU u).Finite)
    (L : LineBundle U) (P : LineBundle V) (N : W.Modules)
    (e : L.sheaf.restrict a ≅ N) (d : P.sheaf.restrict b ≅ N) :
    Module.Finite K (Sections kW N ⊤ ⧸
      ((chartMap kU kW a hka L.sheaf e).range ⊔
        (chartMap kV kW b hkb P.sheaf d).range)) := by
  let := polynomialModule kU u L.sheaf ⊤
  let := polynomialModule kV v P.sheaf ⊤
  let := polynomialModule kW (a.appTop u) N ⊤
  let := polynomialTower kU u L.sheaf ⊤
  let := polynomialTower kV v P.sheaf ⊤
  let := polynomialTower kW (a.appTop u) N ⊤
  let : Module.Finite K[X] (Sections kU L.sheaf ⊤) := polynomial_finite kU u L hu
  let F := chartPolynomialMap kU kW a hka L.sheaf e u
  let G := chartMap kV kW b hkb P.sheaf d
  let : IsLocalizedModule.Away (Polynomial.X : K[X]) F :=
    chartPolynomialMap_localize kU kW a hka L.sheaf e u ha
  have hInv (y : Sections kV P.sheaf ⊤) :
      (Polynomial.X : K[X]) • G ((Polynomial.X : K[X]) • y) = G y := by
    change (Polynomial.eval₂RingHom kW (a.appTop u)) Polynomial.X •
      G ((Polynomial.eval₂RingHom kV v) Polynomial.X • y) = G y
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [chartMap_smul, ← mul_smul, huv, one_smul]
  have hDen (x : Sections kW N ⊤) : ∃ n : ℕ, ∃ y : Sections kV P.sheaf ⊤,
      (Polynomial.X : K[X])^n • G y = x := by
    let : Module Γ(V,⊤) (OpenSections N ⊤) :=
      Module.compHom (OpenSections N ⊤) b.appTop.hom
    let G' := chartModuleMap P.sheaf b d
    let : IsLocalizedModule.Away v G' := chartModuleMap_localize P.sheaf b d v hb
    obtain ⟨n,y,hy⟩ := (inferInstance : IsLocalizedModule.Away v G').surj _ _ x
    refine ⟨n,y,?_⟩
    change (Polynomial.eval₂RingHom kW (a.appTop u)) (Polynomial.X^n) • G y = x
    simp only [map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    change b.appTop (v^n) • (x : OpenSections N ⊤) = G' y at hy
    change (a.appTop u)^n • (G' y : OpenSections N ⊤) = x
    erw [← hy, map_pow, ← mul_smul, ← mul_pow, huv, one_pow, one_smul]
  exact LaurentCech.cokernel_finite F G hInv hDen
end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X : Scheme.{0}}

def twoBaseImage (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens) :
    Submodule K (Sections k M (U ⊓ V)) :=
  (res k M (show U ⊓ V ≤ U from inf_le_left)).range ⊔
    (res k M (show U ⊓ V ≤ V from inf_le_right)).range

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K : Type} [Field K] {X : Scheme.{0}}

def twoBaseCohomologyOne [IsNoetherian X] (k : K →+* Γ(X,⊤))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hc : U ⊔ V = ⊤) :
    letI := Module.compHom (cohomology M 1) k
    (Sections k M (U ⊓ V) ⧸ twoBaseImage k M U V) ≃ₗ[K] cohomology M 1 := by
  letI : Algebra K Γ(X,⊤) := k.toAlgebra
  letI := Module.compHom (cohomology M 1) k
  letI : IsScalarTower K Γ(X,⊤) (cohomology M 1) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  letI : Module K (OpenSections M (U ⊓ V)) := Module.compHom _ k
  letI : IsScalarTower K Γ(X,⊤) (OpenSections M (U ⊓ V)) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  have he : twoBaseImage k M U V = (twoChartImage M U V).restrictScalars K := by
    apply Submodule.ext
    intro x
    change x ∈ twoBaseImage k M U V ↔
      (x : OpenSections M (U ⊓ V)) ∈ twoChartImage M U V
    simp only [twoBaseImage, twoChartImage]
    constructor
    · intro hx
      obtain ⟨y, hy, z, hz, h⟩ :=
        (Submodule.mem_sup (R := K) (M := Sections k M (U ⊓ V))).mp hx
      exact (Submodule.mem_sup (R := Γ(X,⊤)) (M := OpenSections M (U ⊓ V))).mpr
        ⟨y, hy, z, hz, h⟩
    · intro hx
      obtain ⟨y, hy, z, hz, h⟩ :=
        (Submodule.mem_sup (R := Γ(X,⊤)) (M := OpenSections M (U ⊓ V))).mp hx
      exact (Submodule.mem_sup (R := K) (M := Sections k M (U ⊓ V))).mpr
        ⟨y, hy, z, hz, h⟩
  let E := Submodule.Quotient.restrictScalarsEquiv K (twoChartImage M U V)
  let F := (twoAffineCohomologyOne M U V hU hV hc).restrictScalars K
  rw [he]
  exact E.trans F
end PiExponentSeshadri.Geometry.BaseSections

end

end OAI
