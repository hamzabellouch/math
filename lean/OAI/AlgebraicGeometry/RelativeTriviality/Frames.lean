import Mathlib

namespace OAI

noncomputable section

namespace CampanaPeternellSix.RelativeCech
section
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
lemma clear_residue_denominator (c : p.ResidueField) :
    ∃ d : R, d ∉ p ∧ ∃ a : R, algebraMap R p.ResidueField d * c = algebraMap R p.ResidueField a := by
  obtain ⟨x,rfl⟩ := IsLocalRing.residue_surjective (R := Localization.AtPrime p) c
  obtain ⟨⟨a,d⟩,rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
  refine ⟨d,d.property,a,?_⟩
  simpa only [IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq, map_mul] using
    congrArg (IsLocalRing.residue (Localization.AtPrime p))
      (IsLocalization.mk'_spec' (Localization.AtPrime p) a d)

variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [Module p.ResidueField N] [IsScalarTower R p.ResidueField N]
lemma clear_section_denominator (f : M →ₗ[R] N) (hf : IsBaseChange p.ResidueField f) (x : N) :
    ∃ d : R, d ∉ p ∧ ∃ a : M, f a = algebraMap R p.ResidueField d • x := by
  induction x using hf.inductionOn with
  | tmul m => exact ⟨1, p.primeCompl.one_mem, m, by simp⟩
  | add x y hx hy =>
    obtain ⟨d,hd,a,ha⟩ := hx
    obtain ⟨e,he,b,hb⟩ := hy
    refine ⟨d*e,p.primeCompl.mul_mem hd he,e • a + d • b,?_⟩
    simp only [map_add,map_smul,ha,hb,map_mul,smul_add,mul_smul]
    rw [← IsScalarTower.algebraMap_smul p.ResidueField e, ← IsScalarTower.algebraMap_smul p.ResidueField d]
    simp only [smul_comm (algebraMap R p.ResidueField e) (algebraMap R p.ResidueField d)]
  | smul c x hx =>
    obtain ⟨d,hd,a,ha⟩ := hx
    obtain ⟨e,he,b,hb⟩ := clear_residue_denominator p c
    refine ⟨d*e,p.primeCompl.mul_mem hd he,b • a,?_⟩
    rw [map_smul,ha,← IsScalarTower.algebraMap_smul p.ResidueField b,← hb,map_mul]
    simp only [mul_smul,smul_comm (algebraMap R p.ResidueField d)]
end

open scoped BigOperators TensorProduct
universe u
variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [Module p.ResidueField N] [IsScalarTower R p.ResidueField N]
theorem clear_finite_sections_denominator (f : M →ₗ[R] N) (hf : IsBaseChange p.ResidueField f)
    (I : Type u) [Finite I] (s : I → N) :
    ∃ d : R, d ∉ p ∧ ∃ t : I → M, ∀ i, f (t i) = algebraMap R p.ResidueField d • s i := by
  classical
  let := Fintype.ofFinite I
  choose d hd t ht using fun i => clear_section_denominator p f hf (s i)
  refine ⟨∏ i, d i, ?_, fun i => (∏ j ∈ Finset.univ.erase i, d j) • t i, ?_⟩
  · exact p.primeCompl.prod_mem (fun i _ => hd i)
  · intro i
    rw [map_smul,ht,← IsScalarTower.algebraMap_smul p.ResidueField]
    rw [← mul_smul,← map_mul,Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
end CampanaPeternellSix.RelativeCech

namespace CampanaPeternellSix.FiberFrame
section
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}} (E : X.Modules)
def sectionsTopEquiv : E.sections ≃ Γ(E,⊤) where
  toFun s := s.val (op ⊤)
  invFun x := E.val.sectionsMk (fun U => E.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op x)
    (fun U V f => by
      erw [← PresheafOfModules.map_comp_apply]
      rfl)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  right_inv x := by
    change E.val.map (𝟙 (op ⊤)) x = x
    simp
    rfl
lemma sectionsTopEquiv_naturality {F : X.Modules} (f : E ⟶ F) (s : E.sections) :
    sectionsTopEquiv F (SheafOfModules.sectionsMap f s) = f.app ⊤ (sectionsTopEquiv E s) := rfl
lemma sectionsTopEquiv_symm_apply (s : Γ(E,⊤)) (U : X.Opens) :
    ((sectionsTopEquiv E).symm s).val (op U) = E.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s := rfl
end

section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules TopologicalSpace
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {E : Y.Modules} {I : Type u}
instance inverseOpens_final : (Opens.map f.base).Final := by
  let F := Opens.map f.base
  let : (Functor.fromPUnit.{0} (⊤ : Y.Opens)).Final :=
    Functor.final_fromPUnit_of_isTerminal Limits.isTerminalTop
  let : (Functor.fromPUnit.{0} (⊤ : X.Opens)).Final :=
    Functor.final_fromPUnit_of_isTerminal Limits.isTerminalTop
  let : (Functor.fromPUnit.{0} (⊤ : Y.Opens) ⋙ F).Final :=
    Functor.final_of_natIso (F := Functor.fromPUnit.{0} (⊤ : X.Opens))
      (Discrete.natIso (fun _ => eqToIso (by simp [F])))
  exact Functor.final_of_final_comp (Functor.fromPUnit.{0} (⊤ : Y.Opens)) F

abbrev pullbackFreeIso : (pullback f).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
    SheafOfModules.free I := by
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  exact SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I
lemma pullbackFree_sections (α : SheafOfModules.free I ⟶ E) (i : I) :
    SheafOfModules.pushforwardSections f.toRingCatSheafHom
      (((pullback f).obj E).freeHomEquiv ((pullbackFreeIso f).inv ≫ (pullback f).map α) i) =
      SheafOfModules.sectionsMap ((pullbackPushforwardAdjunction f).unit.app E)
        (E.freeHomEquiv α i) := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  let F := pullback f
  let G := pushforward f
  let A := pullbackPushforwardAdjunction f
  let u := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  let γ := (pullbackFreeIso f).inv ≫ F.map α
  have h : F.map (SheafOfModules.ιFree i ≫ α) = u ≫ SheafOfModules.ιFree i ≫ γ := by
    dsimp [γ, u, F, pullbackFreeIso]
    erw [Functor.map_comp]
    erw [← SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom_assoc]
    erw [Iso.hom_inv_id_assoc]
    rfl
  have ha := congrArg (A.homEquiv _ _) h
  have hb : A.homEquiv _ _ u = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  erw [Adjunction.homEquiv_naturality_right, hb] at ha
  have hc : A.homEquiv _ _ (F.map (SheafOfModules.ιFree i ≫ α)) =
      (SheafOfModules.ιFree i ≫ α) ≫ A.unit.app E := by
    erw [Adjunction.homEquiv_unit]
    exact (A.unit.naturality _).symm
  erw [hc] at ha
  change SheafOfModules.pushforwardSections _
    (((pullback f).obj E).unitHomEquiv (SheafOfModules.ιFree i ≫ γ)) = _
  erw [SheafOfModules.pushforwardSections_unitHomEquiv]
  exact (congrArg (((pushforward f).obj ((pullback f).obj E)).unitHomEquiv) ha.symm).trans
    (SheafOfModules.unitHomEquiv_comp_apply _ _)
end

section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {E : Y.Modules} {I : Type u}
lemma pullbackFree_top (α : SheafOfModules.free I ⟶ E) (i : I) :
    ((pullback f).obj E).presheaf.map
        (homOfLE (show (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ by simp)).op
      (((pullbackPushforwardAdjunction f).unit.app E).app ⊤
        (sectionsTopEquiv E (E.freeHomEquiv α i))) =
      sectionsTopEquiv ((pullback f).obj E)
        (((pullback f).obj E).freeHomEquiv ((pullbackFreeIso f).inv ≫ (pullback f).map α) i) := by
  let s := ((pullback f).obj E).freeHomEquiv ((pullbackFreeIso f).inv ≫ (pullback f).map α) i
  let v := (homOfLE (show (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ by simp)).op
  have h := congrArg (fun t : ((pushforward f).obj ((pullback f).obj E)).sections =>
    ((pullback f).obj E).presheaf.map v (t.val (op ⊤))) (pullbackFree_sections f α i)
  change ((pullback f).obj E).val.map v (s.val (op (f ⁻¹ᵁ ⊤))) = _ at h
  exact h.symm.trans (s.property v)
end

open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}} (E : X.Modules)
def scalarEnd (a : Γ(X,⊤)) : E ⟶ E where
  val.app U := ModuleCat.ofHom
    { toFun := fun m => @SMul.smul (X.ringCatSheaf.obj.obj U) (E.val.obj U) inferInstance
        (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op a) m
      map_add' := fun m n => by
        change Γ(E,U.unop) at m n
        exact smul_add (M := Γ(X,U.unop)) (A := Γ(E,U.unop)) _ m n
      map_smul' := fun b m => by
        change Γ(X,U.unop) at b
        change Γ(E,U.unop) at m
        change (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op a) • (b • m) =
          b • ((X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op a) • m)
        exact smul_comm _ _ _ }
  val.naturality {U V} f := by
    ext m
    change Γ(E,U.unop) at m
    change @SMul.smul Γ(X,V.unop) Γ(E,V.unop) inferInstance
        (X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op a) (E.val.map f m) =
      E.val.map f (@SMul.smul Γ(X,U.unop) Γ(E,U.unop) inferInstance
        (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op a) m)
    erw [E.val.map_smul]
    congr 1
    exact ConcreteCategory.congr_hom (X.presheaf.map_comp _ _) a
lemma scalarEnd_app (a : Γ(X,⊤)) (U : X.Opens) (m : Γ(E,U)) :
    (scalarEnd E a).app U m =
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op a) • m := rfl
lemma scalarEnd_app_top (a : Γ(X,⊤)) (m : Γ(E,⊤)) :
    (scalarEnd E a).app ⊤ m = a • m := by
  change (X.presheaf.map (𝟙 (op ⊤)) a) • m = _
  simp
lemma scalarEnd_mul (a b : Γ(X,⊤)) : scalarEnd E a ≫ scalarEnd E b = scalarEnd E (a*b) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, scalarEnd_app, map_mul]
  rw [mul_smul,smul_comm]
lemma scalarEnd_one : scalarEnd E 1 = 𝟙 E := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  simp [scalarEnd_app]
def scalarIso (a : Γ(X,⊤)ˣ) : E ≅ E where
  hom := scalarEnd E a
  inv := scalarEnd E ↑a⁻¹
  hom_inv_id := by rw [scalarEnd_mul,Units.mul_inv,scalarEnd_one]
  inv_hom_id := by rw [scalarEnd_mul,Units.inv_mul,scalarEnd_one]
end CampanaPeternellSix.FiberFrame

end

end OAI
