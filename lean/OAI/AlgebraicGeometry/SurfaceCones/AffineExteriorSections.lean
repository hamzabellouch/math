import OAI.AlgebraicGeometry.SurfaceCones.HomogeneousEvaluation
import OAI.AlgebraicGeometry.SurfaceCones.CartierSupport

namespace OAI

open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry in
private local instance sectionModule {X : Scheme.{_}}
    (M : X.Modules) (U : X.Opens) : Module Γ(X,U) (M.val.obj (.op U)) :=
  (M.val.obj (.op U)).isModule

/-! The affine exterior comparison on wedge sections. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace AffineExterior
universe u
variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

local instance (U : (Spec (.of R)).Opens) : CommRing (((Spec (.of R)).ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing ((Spec (.of R)).sheaf.obj.obj (.op U)))
local instance (U : (Spec (.of R)).Opens) : Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))
local instance (N : (Spec (.of R)).Modules) (U : (Spec (.of R)).Opens) :
    Module Γ(Spec (.of R),U) Γ(N,U) := (N.val.obj (.op U)).isModule
local instance (N : (Spec (.of R)).Modules) (U : (Spec (.of R)).Opens) : Module R Γ(N,U) :=
  inferInstanceAs (Module R ((modulesSpecToSheaf.obj N).obj.obj (.op U)))

lemma affineMap_unit :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (Spec (.of R)).ringCatSheaf.obj)).unit.app
        (Ω R M) ≫ (affineMap R M).val = moduleMap R M :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec (.of R)).ringCatSheaf.obj)).homEquiv
    (Ω R M) (tilde (R := .of R) (E R M))).apply_symm_apply _

lemma affineMap_basic_wedge (r : R) (z : Fin 2 → M) :
    (affineMap R M).val.app (.op (PrimeSpectrum.basicOpen r))
      (ActualExterior.wedgeSection (tilde (R := .of R) M) 2 (PrimeSpectrum.basicOpen r)
        (fun i => tilde.toOpen (R := .of R) M (PrimeSpectrum.basicOpen r) (z i))) =
      tilde.toOpen (R := .of R) (E R M) (PrimeSpectrum.basicOpen r)
        (ModuleCat.exteriorPower.mk z) := by
  let : Module Γ(Spec (.of R),PrimeSpectrum.basicOpen r)
      ((tilde (R := .of R) M).val.obj (.op (PrimeSpectrum.basicOpen r))) :=
    ((tilde (R := .of R) M).val.obj (.op (PrimeSpectrum.basicOpen r))).isModule
  have h := congrArg (fun b : Ω R M ⟶ (tilde (R := .of R) (E R M)).val =>
    b.app (.op (PrimeSpectrum.basicOpen r))
      (exteriorPower.ιMulti Γ(Spec (.of R),PrimeSpectrum.basicOpen r) 2
        (fun i => tilde.toOpen (R := .of R) M (PrimeSpectrum.basicOpen r) (z i)))) (affineMap_unit R M)
  refine h.trans ?_
  change (additive R M).app (.op (PrimeSpectrum.basicOpen r)) _ = _
  erw [additive_basic]
  exact basicMap_mk R M r z

lemma affineMap_top_wedge (z : Fin 2 → M) :
    (affineMap R M).val.app (.op ⊤)
      (ActualExterior.wedgeSection (tilde (R := .of R) M) 2 ⊤
        (fun i => tilde.toOpen (R := .of R) M ⊤ (z i))) =
      tilde.toOpen (R := .of R) (E R M) ⊤ (ModuleCat.exteriorPower.mk z) := by
  have he : PrimeSpectrum.basicOpen (1 : R) = (⊤ : (Spec (.of R)).Opens) :=
    PrimeSpectrum.basicOpen_one
  let P (U : (Spec (.of R)).Opens) : Prop :=
    (affineMap R M).val.app (.op U)
      (ActualExterior.wedgeSection (tilde (R := .of R) M) 2 U
        (fun i => tilde.toOpen (R := .of R) M U (z i))) =
      tilde.toOpen (R := .of R) (E R M) U (ModuleCat.exteriorPower.mk z)
  exact (congrArg P he).mp (affineMap_basic_wedge R M 1 z)

end AffineExterior

end

/-! Top differential sections under the open affine exterior comparison. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualExterior
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
local instance (U : X.Opens) : CommRing ((X.ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing (X.sheaf.obj.obj (.op U)))
local instance (U : Y.Opens) : CommRing ((Y.ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing (Y.sheaf.obj.obj (.op U)))

lemma openIso_inv_wedgeSection (M : Y.Modules) (n : ℕ) (U : X.Opens)
    (z : Fin n → Γ(M,f ''ᵁ U)) :
    (openIso f M n).inv.val.app (.op U) (wedgeSection (M.restrict f) n U z) =
      wedgeSection M n (f ''ᵁ U) z := by
  rw [← openIso_wedgeSection f M n U z]
  exact congrArg (fun a : ((sheafFunctor Y n).obj M).restrict f ⟶
      ((sheafFunctor Y n).obj M).restrict f =>
    a.val.app (.op U) (wedgeSection M n (f ''ᵁ U) z)) (openIso f M n).hom_inv_id
end ActualExterior
namespace AffineExterior
universe u
variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
local instance (U : (Spec (.of R)).Opens) : CommRing (((Spec (.of R)).ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing ((Spec (.of R)).sheaf.obj.obj (.op U)))

lemma affineIso_inv_top_wedge (z : Fin 2 → M) :
    (affineIso R M).inv.val.app (.op ⊤)
      (tilde.toOpen (R := .of R) (E R M) ⊤ (ModuleCat.exteriorPower.mk z)) =
      ActualExterior.wedgeSection (tilde (R := .of R) M) 2 ⊤
        (fun i => tilde.toOpen (R := .of R) M ⊤ (z i)) := by
  rw [← affineMap_top_wedge R M z]
  exact ActualSections.iso_inv_hom_apply (affineIso R M) ⊤ _

end AffineExterior
namespace ActualExterior
universe u
variable {Y : Scheme.{u}} (R : Type u) [CommRing R]
  (i : Spec (.of R) ⟶ Y) [IsOpenImmersion i]
  (M : Y.Modules) (N : ModuleCat.{u} R)
local instance (U : (Spec (.of R)).Opens) : CommRing (((Spec (.of R)).ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing ((Spec (.of R)).sheaf.obj.obj (.op U)))
local instance (U : Y.Opens) : CommRing ((Y.ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing (Y.sheaf.obj.obj (.op U)))

/-- The comparison of the top exterior sheaf on an affine open. -/
def openAffineIso (e : M.restrict i ≅ tilde N) :
    ((sheafFunctor Y 2).obj M).restrict i ≅ tilde (N.exteriorPower 2) :=
  openIso i M 2 ≪≫ (sheafFunctor (Spec (.of R)) 2).mapIso e ≪≫
    AffineExterior.affineIso R N

lemma openAffineIso_inv_wedge (e : M.restrict i ≅ tilde N) (z : Fin 2 → N) :
    (openAffineIso R i M N e).inv.val.app (.op ⊤)
      (tilde.toOpen (R := .of R) (N.exteriorPower 2) ⊤ (ModuleCat.exteriorPower.mk z)) =
      wedgeSection M 2 (i ''ᵁ ⊤)
        (fun j => e.inv.val.app (.op ⊤) (tilde.toOpen (R := .of R) N ⊤ (z j))) := by
  change (openIso i M 2).inv.val.app (.op ⊤)
    (((sheafFunctor (Spec (.of R)) 2).map e.inv).val.app (.op ⊤)
      ((AffineExterior.affineIso R N).inv.val.app (.op ⊤)
        (tilde.toOpen (R := .of R) (N.exteriorPower 2) ⊤ (ModuleCat.exteriorPower.mk z)))) = _
  have h₁ := AffineExterior.affineIso_inv_top_wedge R N z
  have h₂ := map_wedgeSection e.inv 2 ⊤
    (fun j => tilde.toOpen (R := .of R) N ⊤ (z j))
  have h₃ := openIso_inv_wedgeSection i M 2 ⊤
    (fun j => e.inv.val.app (.op ⊤) (tilde.toOpen (R := .of R) N ⊤ (z j)))
  exact (congrArg (fun x => (openIso i M 2).inv.val.app (.op ⊤)
      (((sheafFunctor (Spec (.of R)) 2).map e.inv).val.app (.op ⊤) x)) h₁).trans
    ((congrArg (fun x => (openIso i M 2).inv.val.app (.op ⊤) x) h₂).trans h₃)
end ActualExterior

end

noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualExterior
universe u
variable {Y : Scheme.{u}} (R : Type u) [CommRing R]
  (i : Spec (.of R) ⟶ Y) [IsOpenImmersion i]
  (M : Y.Modules) (N : ModuleCat.{u} R)
local instance (U : (Spec (.of R)).Opens) : CommRing (((Spec (.of R)).ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing ((Spec (.of R)).sheaf.obj.obj (.op U)))
local instance (U : Y.Opens) : CommRing ((Y.ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing (Y.sheaf.obj.obj (.op U)))
lemma openAffineInv_eval_wedge (e : M.restrict i ≅ tilde N) (z : Fin 2 → N) :
    ActualSections.isoInv (openAffineIso R i M N e) ⊤
      (tilde.toOpen (R := .of R) (N.exteriorPower 2) ⊤ (ModuleCat.exteriorPower.mk z)) =
      wedgeSection M 2 (i ''ᵁ ⊤)
        (fun j => ActualSections.isoInv e ⊤ (tilde.toOpen (R := .of R) N ⊤ (z j))) :=
  openAffineIso_inv_wedge R i M N e z
end ActualExterior

end

/-! Sections and scalar actions induced by affine sheaf frames. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
universe u
variable {Y : Scheme.{u}} (R : Type u) [CommRing R]
  (i : Spec (.of R) ⟶ Y) [IsOpenImmersion i]
  (M : Y.Modules) (N : ModuleCat.{u} R) (e : M.restrict i ≅ tilde N)
local instance (U : (Spec (.of R)).Opens) : Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))
local instance (U : Y.Opens) : CommRing ((Y.ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing (Y.sheaf.obj.obj (.op U)))
local instance (U : (Spec (.of R)).Opens) : CommRing (((Spec (.of R)).ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing ((Spec (.of R)).sheaf.obj.obj (.op U)))

local instance (U : (Spec (.of R)).Opens) : Module Γ(Spec (.of R),U)
    ((modulesSpecToSheaf.obj (tilde (R := CommRingCat.of R) N)).presheaf.obj (.op U)) :=
  ((tilde (R := CommRingCat.of R) N).val.obj (.op U)).isModule

def affineSection (n : N) : Γ(M,i ''ᵁ ⊤) :=
  e.inv.val.app (.op ⊤) (tilde.toOpen (R := .of R) N ⊤ n)

lemma affineSection_zero : affineSection R i M N e 0 = 0 := by
  unfold affineSection
  erw [map_zero, map_zero]
  rfl
lemma affineSection_add (m n : N) :
    affineSection R i M N e (m+n) = affineSection R i M N e m + affineSection R i M N e n := by
  unfold affineSection
  erw [map_add, map_add]
  rfl
lemma affineSection_smul (r : R) (n : N) :
    affineSection R i M N e (r • n) =
      (i.appIso ⊤).inv (algebraMap R Γ(Spec (.of R),⊤) r) • affineSection R i M N e n := by
  unfold affineSection
  erw [map_smul]
  change e.inv.val.app (.op ⊤)
    (algebraMap R Γ(Spec (.of R),⊤) r • (tilde.toOpen (R := .of R) N ⊤ n : Γ(tilde (R := CommRingCat.of R) N,⊤))) = _
  erw [map_smul]
  rfl
end ActualSections

end

/-! Top differential sections on affine opens and their coordinate formulas. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCotangent
universe u
variable {k : Type u} [CommRing k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
  (R : Type u) [CommRing R] [Algebra k R]
  (i : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion i]
  (h : i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k R)))
local instance (U : (Spec (.of R)).Opens) : Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))
local instance (U : Y.Opens) : CommRing ((Y.ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing (Y.sheaf.obj.obj (.op U)))
local instance (U : (Spec (.of R)).Opens) : CommRing (((Spec (.of R)).ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing ((Spec (.of R)).sheaf.obj.obj (.op U)))

/-- The top exterior power of the cotangent sheaf. -/
def topSheaf : Y.Modules := (ActualExterior.sheafFunctor Y 2).obj (sheaf g)

/-- The affine coordinate functions on their image in Y. -/
def chartCoordinate : R →+* Γ(Y, i ''ᵁ ⊤) :=
  (i.appIso ⊤).inv.hom.comp (algebraMap R Γ(Spec (.of R),⊤))

/-- The intrinsic comparison on an affine open. -/
def topOpenAffineIso : (topSheaf g).restrict i ≅
    tilde ((affineModule (k := k) R).exteriorPower 2) :=
  ActualExterior.openAffineIso R i (sheaf g) (affineModule (k := k) R)
    (openAffineIso g R i h)

/-- Send a algebraic top differential to its intrinsic sheaf section. -/
def topChartSection (m : (affineModule (k := k) R).exteriorPower 2) :
    Γ(topSheaf g, i ''ᵁ ⊤) :=
  ActualSections.isoInv (topOpenAffineIso g R i h) ⊤
    (tilde.toOpen (R := .of R) ((affineModule (k := k) R).exteriorPower 2) ⊤ m)

lemma topChartSection_volume (a : Fin 2 → R) :
    topChartSection g R i h (ModuleCat.exteriorPower.mk (fun j => KaehlerDifferential.D k R (a j))) =
      ActualExterior.wedgeSection (sheaf g) 2 (i ''ᵁ ⊤)
        (fun j => (derivation g).d (chartCoordinate R i (a j))) := by
  unfold topChartSection topOpenAffineIso
  erw [ActualExterior.openAffineInv_eval_wedge]
  congr 1
  funext j
  exact openAffineIso_inv_D g R i h (a j)

lemma topChartSection_zero : topChartSection g R i h 0 = 0 := by
  exact ActualSections.affineSection_zero R i (topSheaf g) _ (topOpenAffineIso g R i h)

lemma topChartSection_add (a b : (affineModule (k := k) R).exteriorPower 2) :
    topChartSection g R i h (a+b) = topChartSection g R i h a + topChartSection g R i h b := by
  exact ActualSections.affineSection_add R i (topSheaf g) _ (topOpenAffineIso g R i h) a b

lemma topChartSection_smul (r : R) (m : (affineModule (k := k) R).exteriorPower 2) :
    topChartSection g R i h (r • m) =
      chartCoordinate R i r • topChartSection g R i h m := by
  exact ActualSections.affineSection_smul R i (topSheaf g) _ (topOpenAffineIso g R i h) r m

end ActualCotangent

end

/-! Restriction of coordinates between commuting affine open charts. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
universe u
variable {A B Y : Scheme.{u}} (i : A ⟶ Y) (j : B ⟶ Y) (f : B ⟶ A)
  [IsOpenImmersion i] [IsOpenImmersion j] (hf : f ≫ i = j)
  (h : j ''ᵁ ⊤ ≤ i ''ᵁ ⊤)

include hf in
lemma chart_coordinate_square :
    Y.presheaf.map (homOfLE h).op ≫ (j.appIso ⊤).hom =
      (i.appIso ⊤).hom ≫ f.appTop := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appIso_hom']
  have he := Scheme.Hom.appLE_comp_appLE f i (i ''ᵁ ⊤) ⊤ ⊤
    (i.preimage_image_eq ⊤).ge (show (⊤ : B.Opens) ≤ f ⁻¹ᵁ ⊤ from le_rfl)
  simp only [hf] at he
  have ht : f.appLE ⊤ ⊤ le_rfl = f.appTop := by
    change f.appTop ≫ B.presheaf.map (𝟙 _) = _
    rw [B.presheaf.map_id, Category.comp_id]
  rw [ht] at he
  exact he.symm

include hf in
lemma chart_coordinate_restrict (a : Γ(A,⊤)) :
    Y.presheaf.map (homOfLE h).op ((i.appIso ⊤).inv a) =
      (j.appIso ⊤).inv (f.appTop a) := by
  have he : (i.appIso ⊤).inv ≫ Y.presheaf.map (homOfLE h).op =
      f.appTop ≫ (j.appIso ⊤).inv := by
    apply (cancel_mono (j.appIso ⊤).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [chart_coordinate_square i j f hf h, Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom he a

end ActualSections

end

/-! Naturality of affine coordinate values under Spec maps. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
local instance specMapSectionsAlgebra (R : Type u) [CommRing R] (U : (Spec (.of R)).Opens) : Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))
lemma specMap_algebraMap (f : A →+* B) (a : A) :
    (Spec.map (CommRingCat.ofHom f)).appTop (algebraMap A Γ(Spec (.of A),⊤) a) =
      algebraMap B Γ(Spec (.of B),⊤) (f a) := by
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm a
end ActualSections

end

/-! Restriction of affine scalar coordinates. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
universe u
variable {A B : Type u} [CommRing A] [CommRing B] {Y : Scheme.{u}}
local instance affineCoordinateRestrictionAlgebra (R : Type u) [CommRing R] (U : (Spec (.of R)).Opens) : Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))
lemma affine_coordinate_restrict (i : Spec (.of A) ⟶ Y) (j : Spec (.of B) ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (f : A →+* B)
    (hf : Spec.map (CommRingCat.ofHom f) ≫ i = j)
    (h : j ''ᵁ ⊤ ≤ i ''ᵁ ⊤) (a : A) :
    Y.presheaf.map (homOfLE h).op
        ((i.appIso ⊤).inv (algebraMap A Γ(Spec (.of A),⊤) a)) =
      (j.appIso ⊤).inv (algebraMap B Γ(Spec (.of B),⊤) (f a)) := by
  erw [chart_coordinate_restrict i j _ hf h, specMap_algebraMap]
  rfl
end ActualSections

end

/-! Canonical differentials commute with affine open restriction. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCotangent
universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
  (i : Spec (.of A) ⟶ Y) (j : Spec (.of B) ⟶ Y)
  [IsOpenImmersion i] [IsOpenImmersion j]
  (hi : i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k A)))
  (hj : j ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k B)))
  (hf : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ i = j)
  (h : j ''ᵁ ⊤ ≤ i ''ᵁ ⊤)
local instance (R : Type u) [CommRing R] (U : (Spec (.of R)).Opens) : Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))
local instance (U : Y.Opens) : CommRing ((Y.ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing (Y.sheaf.obj.obj (.op U)))

include hf in
lemma chartCoordinate_restrict (a : A) :
    Y.presheaf.map (homOfLE h).op (chartCoordinate A i a) =
      chartCoordinate B j (algebraMap A B a) := by
  exact ActualSections.affine_coordinate_restrict i j _ hf h a

include hf in
omit [IsScalarTower k A B] in
lemma topChartSection_volume_restrict (a : Fin 2 → A) :
    (topSheaf g).val.map (homOfLE h).op
        (topChartSection g A i hi (ModuleCat.exteriorPower.mk
          (fun q => KaehlerDifferential.D k A (a q)))) =
      topChartSection g B j hj (ModuleCat.exteriorPower.mk
          (fun q => KaehlerDifferential.D k B (algebraMap A B (a q)))) := by
  rw [topChartSection_volume, topChartSection_volume]
  change ((ActualExterior.sheafFunctor Y 2).obj (sheaf g)).val.map (homOfLE h).op _ = _
  erw [ActualExterior.wedgeSection_map]
  congr 1
  funext q
  erw [← (derivation g).d_map, chartCoordinate_restrict i j hf h]

end ActualCotangent

end

/-! Extension of coordinate-differential comparisons to all top forms. -/
noncomputable section
namespace ActualSections
variable {R M N S : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Monoid S] [DistribMulAction S N]
lemma eq_of_span_eq_top (s : Set M) (hs : Submodule.span R s = ⊤)
    (φ : R → S) (f g : M → N)
    (h0 : f 0 = g 0)
    (hfadd : ∀ a b, f (a+b) = f a + f b)
    (hgadd : ∀ a b, g (a+b) = g a + g b)
    (hfscalar : ∀ r a, f (r • a) = φ r • f a)
    (hgscalar : ∀ r a, g (r • a) = φ r • g a)
    (hgen : ∀ a ∈ s, f a = g a) : ∀ a, f a = g a := by
  intro a
  have ha : a ∈ Submodule.span R s := by rw [hs]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha => exact hgen a ha
  | zero => exact h0
  | add a b ha hb hfa hfb => rw [hfadd, hgadd, hfa, hfb]
  | smul r a ha hfa => rw [hfscalar, hgscalar, hfa]
end ActualSections


/-! Affine top differential comparison on arbitrary sections. -/
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite Module KaehlerDifferential
namespace ActualCotangent
universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
  {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
  (i : Spec (.of A) ⟶ Y) (j : Spec (.of B) ⟶ Y)
  [IsOpenImmersion i] [IsOpenImmersion j]
  (hi : i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k A)))
  (hj : j ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k B)))
  (hf : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ i = j)
  (h : j ''ᵁ ⊤ ≤ i ''ᵁ ⊤)
local instance formRestrictionAffineAlgebra (R : Type u) [CommRing R]
    (U : (Spec (.of R)).Opens) : Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))
local instance formRestrictionCommRing (U : Y.Opens) : CommRing ((Y.ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing (Y.sheaf.obj.obj (.op U)))
include hf in
lemma topChartSection_restrict (m : ⋀[A]^2 Ω[A⁄k]) :
    (topSheaf g).val.map (homOfLE h).op (topChartSection g A i hi m) =
      topChartSection g B j hj (CanonicalCoordinates.topDifferentialMap k A B m) := by
  let f : (⋀[A]^2 Ω[A⁄k]) → Γ(topSheaf g, j ''ᵁ ⊤) := fun m =>
    (topSheaf g).val.map (homOfLE h).op (topChartSection g A i hi m)
  let q : (⋀[A]^2 Ω[A⁄k]) → Γ(topSheaf g, j ''ᵁ ⊤) := fun m =>
    topChartSection g B j hj (CanonicalCoordinates.topDifferentialMap k A B m)
  apply ActualSections.eq_of_span_eq_top _
    (exteriorPower.ιMulti_span_of_span A 2 Ω[A⁄k] (KaehlerDifferential.span_range_derivation k A))
    (fun r => chartCoordinate B j (algebraMap A B r)) f q
  · dsimp only [f,q]
    erw [topChartSection_zero, map_zero, map_zero, topChartSection_zero]
    rfl
  · intro a b
    dsimp only [f]
    erw [topChartSection_add, map_add]
    rfl
  · intro a b
    dsimp only [q]
    erw [map_add, topChartSection_add]
  · intro r a
    dsimp only [f]
    erw [topChartSection_smul]
    exact ((topSheaf g).val.map_smul (homOfLE h).op
      (chartCoordinate A i r) (topChartSection g A i hi a)).trans
      (congrArg (fun c : Γ(Y,j ''ᵁ ⊤) => c • f a)
        (chartCoordinate_restrict i j hf h r))
  · intro r a
    dsimp only [q]
    erw [map_smul]
    change topChartSection g B j hj
      ((algebraMap A B r) • CanonicalCoordinates.topDifferentialMap k A B a) = _
    erw [topChartSection_smul]
  · rintro _ ⟨u, hu, rfl⟩
    choose a ha using fun i => hu (Set.mem_range_self i)
    have hu' : u = fun i => D k A (a i) := funext (fun i => (ha i).symm)
    rw [hu']
    dsimp only [f,q]
    rw [CanonicalCoordinates.topDifferentialMap_volume]
    exact topChartSection_volume_restrict g i j hi hj hf h a
end ActualCotangent

end

/-! The scalar action on module-sheaf sections. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSections
universe u
variable {X : Scheme.{u}}
local instance sectionScalarCommRing (U : X.Opens) : CommRing ((X.ringCatSheaf.obj).obj (.op U)) :=
  inferInstanceAs (CommRing (X.sheaf.obj.obj (.op U)))
def scalarMul (M : X.Modules) (U : X.Opens) (r : Γ(X,U)) (m : Γ(M,U)) : Γ(M,U) := r • m
lemma scalarMul_congr (M : X.Modules) (U : X.Opens) (r : Γ(X,U))
    {m n : Γ(M,U)} (h : m = n) : scalarMul M U r m = scalarMul M U r n :=
  congrArg (scalarMul M U r) h
end ActualSections

end

noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCotangent
universe u
variable {k : Type u} [CommRing k] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k))
  (R : Type u) [CommRing R] [Algebra k R]
  (i : Spec (CommRingCat.of R) ⟶ Y) [IsOpenImmersion i]
  (h : i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k R)))
lemma topChartSection_scalar (r : R) (m : (affineModule (k := k) R).exteriorPower 2) :
    topChartSection g R i h (r • m) =
      ActualSections.scalarMul (topSheaf g) (i ''ᵁ ⊤) (chartCoordinate R i r)
        (topChartSection g R i h m) := topChartSection_smul g R i h r m
end ActualCotangent

end

/-! Canonical frame sections and their transition equations on chart intersections. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite Module KaehlerDifferential
namespace SourceSymmetry
open ExplicitCone CanonicalCoordinates
local instance coeffIntrinsicKaehler (A : Subalgebra ℂ L) : Module A Ω[A⁄ℂ] := kaehlerModule ℂ A
local instance coeffIntrinsicTop (A : Subalgebra ℂ L) : Module A (⋀[A]^2 Ω[A⁄ℂ]) := topModule _ _
local instance coeffIntrinsicTopSmul (A : Subalgebra ℂ L) : SMul A (⋀[A]^2 Ω[A⁄ℂ]) :=
  (topModule _ _).toSMul

lemma coefficientOverlapIota_toComplex (s t : SectionIndex) (hs : Good s) :
    coefficientOverlapIota s t hs ≫ projectiveSurfaceToComplex =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (coefficientOverlap s t))) := by
  rw [← coefficientOverlapIota_left s t hs, Category.assoc, coefficientIota_toComplex,
    ← Spec.map_comp]
  congr 1


lemma coefficientOverlap_le_left (s t : SectionIndex) (hs : Good s) :
    coefficientOverlapIota s t hs ''ᵁ ⊤ ≤ coefficientIota s hs ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange,
    coefficientOverlapIota_opensRange, coefficientIota_opensRange]
  exact inf_le_left


lemma coefficientOverlap_le_right (s t : SectionIndex) (hs : Good s) (ht : Good t) :
    coefficientOverlapIota s t hs ''ᵁ ⊤ ≤ coefficientIota t ht ''ᵁ ⊤ := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange,
    coefficientOverlapIota_opensRange, coefficientIota_opensRange]
  exact inf_le_right


/-- The canonical generator, as a section of the intrinsic ∧² Ω. -/
def canonicalFrameSection (s : SectionIndex) (hs : Good s) :
    Γ(canonicalSheaf, coefficientIota s hs ''ᵁ ⊤) :=
  ActualCotangent.topChartSection projectiveSurfaceToComplex (coefficientChart s)
    (coefficientIota s hs) (coefficientIota_toComplex s hs) (coefficientCanonicalGenerator s hs)


/-- The intrinsic sheaf interpretation of an algebraic top form on the
intersection. -/
def canonicalOverlapSection (s t : SectionIndex) (hs : Good s)
    (m : ⋀[coefficientOverlap s t]^2 Ω[coefficientOverlap s t⁄ℂ]) :
    Γ(canonicalSheaf, coefficientOverlapIota s t hs ''ᵁ ⊤) :=
  ActualCotangent.topChartSection projectiveSurfaceToComplex (coefficientOverlap s t)
    (coefficientOverlapIota s t hs) (coefficientOverlapIota_toComplex s t hs) m


lemma canonicalFrameSection_restrict_left (s t : SectionIndex) (hs : Good s) :
    canonicalSheaf.val.map (homOfLE (coefficientOverlap_le_left s t hs)).op
        (canonicalFrameSection s hs) =
      canonicalOverlapSection s t hs (coefficientTopInclusion (coefficientChart s) (coefficientOverlap s t)
        (coefficientChart_le_overlap_left s t) (coefficientCanonicalGenerator s hs)) := by
  let := Subalgebra.inclusionAlgebra (coefficientChart s) (coefficientOverlap s t)
    (coefficientChart_le_overlap_left s t)
  let := Subalgebra.inclusionTower (coefficientChart s) (coefficientOverlap s t)
    (coefficientChart_le_overlap_left s t)
  exact ActualCotangent.topChartSection_restrict projectiveSurfaceToComplex
    (coefficientIota s hs) (coefficientOverlapIota s t hs) (coefficientIota_toComplex s hs)
    (coefficientOverlapIota_toComplex s t hs) (coefficientOverlapIota_left s t hs)
    (coefficientOverlap_le_left s t hs) (coefficientCanonicalGenerator s hs)


lemma canonicalFrameSection_restrict_right (s t : SectionIndex) (hs : Good s) (ht : Good t) :
    canonicalSheaf.val.map (homOfLE (coefficientOverlap_le_right s t hs ht)).op
        (canonicalFrameSection t ht) =
      canonicalOverlapSection s t hs (coefficientTopInclusion (coefficientChart t) (coefficientOverlap s t)
        (coefficientChart_le_overlap_right s t) (coefficientCanonicalGenerator t ht)) := by
  let := Subalgebra.inclusionAlgebra (coefficientChart t) (coefficientOverlap s t)
    (coefficientChart_le_overlap_right s t)
  let := Subalgebra.inclusionTower (coefficientChart t) (coefficientOverlap s t)
    (coefficientChart_le_overlap_right s t)
  exact ActualCotangent.topChartSection_restrict projectiveSurfaceToComplex
    (coefficientIota t ht) (coefficientOverlapIota s t hs) (coefficientIota_toComplex t ht)
    (coefficientOverlapIota_toComplex s t hs) (coefficientOverlapIota_right s t hs ht)
    (coefficientOverlap_le_right s t hs ht) (coefficientCanonicalGenerator t ht)


lemma intrinsic_canonical_transition (s t : SectionIndex) (hs : Good s) (ht : Good t) :
    canonicalSheaf.val.map (homOfLE (coefficientOverlap_le_left s t hs)).op
        (canonicalFrameSection s hs) =
      ActualSections.scalarMul canonicalSheaf (coefficientOverlapIota s t hs ''ᵁ ⊤)
        (ActualCotangent.chartCoordinate (coefficientOverlap s t) (coefficientOverlapIota s t hs)
          (canonicalOverlapRatio s t))
        (canonicalSheaf.val.map (homOfLE (coefficientOverlap_le_right s t hs ht)).op
          (canonicalFrameSection t ht)) := by
  have h₁ := canonicalFrameSection_restrict_left s t hs
  have h₂ := canonicalFrameSection_restrict_right s t hs ht
  have h₃ := congrArg (canonicalOverlapSection s t hs)
    (canonical_overlap_transition s t hs ht)
  have h₄ := ActualCotangent.topChartSection_scalar projectiveSurfaceToComplex
    (coefficientOverlap s t) (coefficientOverlapIota s t hs)
    (coefficientOverlapIota_toComplex s t hs) (canonicalOverlapRatio s t)
    (coefficientTopInclusion (coefficientChart t) (coefficientOverlap s t)
      (coefficientChart_le_overlap_right s t) (coefficientCanonicalGenerator t ht))
  exact h₁.trans (h₃.trans (h₄.trans (ActualSections.scalarMul_congr canonicalSheaf
    (coefficientOverlapIota s t hs ''ᵁ ⊤)
    (ActualCotangent.chartCoordinate (coefficientOverlap s t)
      (coefficientOverlapIota s t hs) (canonicalOverlapRatio s t)) h₂.symm)))

end SourceSymmetry

end

/-! Gluing sheaf isomorphisms from matching local frames. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualLineFrames
variable {X : Scheme.{0}}
local instance (U : X.Opens) : CommRing ((X.ringCatSheaf.obj).obj (op U)) :=
  inferInstanceAs (CommRing (X.sheaf.obj.obj (op U)))

def frame {M : X.Modules} {U : X.Opens}
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (h : V ≤ U) : M.val.obj (op V) :=
  e.inv.val.app (op (Over.mk (homOfLE h))) (1 : Γ(X,V))

lemma frame_spans {M : X.Modules} {U : X.Opens}
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (h : V ≤ U) (x : M.val.obj (op V)) :
    @HSMul.hSMul Γ(X,V) Γ(M,V) Γ(M,V) inferInstance
      (e.hom.val.app (op (Over.mk (homOfLE h))) x) (frame e V h) = x := by
  let r : Γ(X,V) := e.hom.val.app (op (Over.mk (homOfLE h))) x
  change @HSMul.hSMul Γ(X,V) Γ(M,V) Γ(M,V) inferInstance
    r (e.inv.val.app (op (Over.mk (homOfLE h))) (1 : Γ(X,V))) = x
  have hm : e.inv.val.app (op (Over.mk (homOfLE h))) (r * 1 : Γ(X,V)) =
      @HSMul.hSMul Γ(X,V) Γ(M,V) Γ(M,V) inferInstance
        r (e.inv.val.app (op (Over.mk (homOfLE h))) (1 : Γ(X,V))) :=
    (e.inv.val.app (op (Over.mk (homOfLE h)))).hom.map_smul r (1 : Γ(X,V))
  have he : e.inv.val.app (op (Over.mk (homOfLE h))) r = x :=
    ConcreteCategory.congr_hom
      (congrArg (fun f => f.val.app (op (Over.mk (homOfLE h)))) e.hom_inv_id) x
  exact hm.symm.trans ((congrArg
    (fun a : Γ(X,V) => e.inv.val.app (op (Over.mk (homOfLE h))) a) (mul_one r)).trans he)

lemma frame_coordinate {M : X.Modules} {U : X.Opens}
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (V : X.Opens) (h : V ≤ U) :
    e.hom.val.app (op (Over.mk (homOfLE h))) (frame e V h) = (1 : Γ(X,V)) :=
  congrArg (fun f : SheafOfModules.unit (X.ringCatSheaf.over U) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over U) =>
    f.val.app (op (Over.mk (homOfLE h))) (1 : Γ(X,V))) e.inv_hom_id

lemma exists_iso_of_matching_frames (M N : X.Modules) {I : Type}
    (U : I → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (eM : ∀ i, M.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (eN : ∀ i, N.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)))
    (hmatch : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      ∃ a : Γ(X,V), frame (eM i) V hi = a • frame (eM j) V hj ∧
        frame (eN i) V hi = a • frame (eN j) V hj) :
    Nonempty (M ≅ N) := by
  let f (i : I) : M.over (U i) ⟶ N.over (U i) := (eM i).hom ≫ (eN i).inv
  have hf : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
      (x : M.val.obj (op V)),
      (f i).val.app (op (Over.mk (homOfLE hi))) x =
        (f j).val.app (op (Over.mk (homOfLE hj))) x := by
    intro i j V hi hj x
    obtain ⟨a, hM, hN⟩ := hmatch i j V hi hj
    let : SMul Γ(X,V) ((M.over (U i)).val.obj (op (Over.mk (homOfLE hi)))) :=
      (sectionModule M V).toSMul
    let : SMul Γ(X,V) ((N.over (U i)).val.obj (op (Over.mk (homOfLE hi)))) :=
      (sectionModule N V).toSMul
    let : SMul Γ(X,V) ((M.over (U j)).val.obj (op (Over.mk (homOfLE hj)))) :=
      (sectionModule M V).toSMul
    let : SMul Γ(X,V) ((N.over (U j)).val.obj (op (Over.mk (homOfLE hj)))) :=
      (sectionModule N V).toSMul
    have fi : (f i).val.app (op (Over.mk (homOfLE hi))) (frame (eM i) V hi) =
        frame (eN i) V hi := by
      change (eN i).inv.val.app (op (Over.mk (homOfLE hi))) ((eM i).hom.val.app (op (Over.mk (homOfLE hi))) (frame (eM i) V hi)) = _
      rw [frame_coordinate]
      rfl
    have fj : (f j).val.app (op (Over.mk (homOfLE hj))) (frame (eM i) V hi) =
        frame (eN i) V hi := by
      erw [hM, map_smul]
      change a • (eN j).inv.val.app (op (Over.mk (homOfLE hj))) ((eM j).hom.val.app (op (Over.mk (homOfLE hj))) (frame (eM j) V hj)) = _
      rw [frame_coordinate]
      exact hN.symm
    let r : Γ(X,V) := (eM i).hom.val.app (op (Over.mk (homOfLE hi))) x
    have hx := frame_spans (eM i) V hi x
    change r • frame (eM i) V hi = x at hx
    erw [← hx, map_smul, map_smul, fi, fj]
    rfl
  obtain ⟨g, hg⟩ := SheafHomGluing.exists_gluing_hom M N U hcover f hf
  have : IsIso g := by
    apply SheafLocality.module_isIso_of_coversTop X.ringCatSheaf
      ((Opens.coversTop_iff X U).mpr hcover)
    intro i
    change IsIso (g.over (U i))
    rw [hg]
    dsimp [f]
    infer_instance
  exact ⟨asIso g⟩
end ActualLineFrames

end

/-! Local sections and their associated line frames. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualLineFrames
variable {X : Scheme.{0}}
local instance (U : X.Opens) : CommRing ((X.ringCatSheaf.obj).obj (op U)) :=
  inferInstanceAs (CommRing (X.sheaf.obj.obj (op U)))

def overFromSection (M : X.Modules) (U : X.Opens) (s : Γ(M,U)) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ M.over U :=
  (M.over U).unitHomEquiv.symm ((M.over U).val.sectionsMk
    (fun V => M.val.map V.unop.hom.op s) (by
      intro V W f
      change M.val.map f.unop.left.op (M.val.map V.unop.hom.op s) =
        M.val.map W.unop.hom.op s
      erw [← PresheafOfModules.map_comp_apply]
      congr 1))

lemma overFromSection_app (M : X.Modules) (U V : X.Opens) (h : V ≤ U)
    (s : Γ(M,U)) (a : Γ(X,V)) :
    (overFromSection M U s).val.app (op (Over.mk (homOfLE h))) a =
      @HSMul.hSMul Γ(X,V) Γ(M,V) Γ(M,V) inferInstance
        a (M.val.map (homOfLE h).op s) := rfl

lemma overFromSection_top (M : X.Modules) (U : X.Opens) (s : Γ(M,U)) :
    (overFromSection M U s).val.app (op (Over.mk (𝟙 U))) (1 : Γ(X,U)) = s := by
  have h := overFromSection_app M U U le_rfl s (1 : Γ(X,U))
  have he : (homOfLE (show U ≤ U from le_rfl)).op = 𝟙 (op U) := Subsingleton.elim _ _
  erw [he, PresheafOfModules.map_id, one_smul] at h
  exact h

lemma overFromSection_frame {M : X.Modules} {U : X.Opens} (s : Γ(M,U))
    [IsIso (overFromSection M U s)] (V : X.Opens) (h : V ≤ U) :
    frame (asIso (overFromSection M U s)).symm V h =
      M.val.map (homOfLE h).op s := by
  change @HSMul.hSMul Γ(X,V) Γ(M,V) Γ(M,V) inferInstance
    (1 : Γ(X,V)) (M.val.map (homOfLE h).op s) = _
  exact @one_smul Γ(X,V) Γ(M,V) _ _ (M.val.map (homOfLE h).op s)
end ActualLineFrames

end

/-! Line frames transported from open-immersion chart inverses. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualLineFrames
universe u
lemma isIso_of_app_bijective {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules R} (f : M ⟶ N)
    (hf : ∀ U, Function.Bijective (f.val.app U)) : IsIso f := by
  let : ∀ U, IsIso (f.val.app U) := fun U =>
    (ConcreteCategory.isIso_iff_bijective _).mpr (hf U)
  let e := PresheafOfModules.isoMk (fun U => asIso (f.val.app U))
    (fun {_ _} h => f.val.naturality h)
  have he : e.hom = f.val := rfl
  have : IsIso f.val := by rw [← he]; infer_instance
  let : IsIso ((SheafOfModules.forget R).map f) := this
  exact isIso_of_reflects_iso f (SheafOfModules.forget _)

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] {M : Y.Modules}
local instance (U : Y.Opens) : CommRing ((Y.ringCatSheaf.obj).obj (op U)) :=
  inferInstanceAs (CommRing (Y.sheaf.obj.obj (op U)))
local instance (U : X.Opens) : CommRing ((X.ringCatSheaf.obj).obj (op U)) :=
  inferInstanceAs (CommRing (X.sheaf.obj.obj (op U)))

local instance restrictedImageModule (V : X.Opens) :
    Module Γ(Y,i ''ᵁ V) ((M.restrict i).val.obj (op V)) :=
  inferInstanceAs (Module Γ(Y,i ''ᵁ V) (M.val.obj (op (i ''ᵁ V))))

def chartFrame (e : M.restrict i ≅ SheafOfModules.unit X.ringCatSheaf) :
    Γ(M,i ''ᵁ ⊤) := e.inv.val.app (op ⊤) (1 : Γ(X,⊤))

lemma chartFrame_restrict (e : M.restrict i ≅ SheafOfModules.unit X.ringCatSheaf)
    (V : X.Opens) :
    M.val.map (homOfLE (i.image_mono (show V ≤ ⊤ from le_top))).op (chartFrame i e) =
      e.inv.val.app (op V) (1 : Γ(X,V)) := by
  have h := PresheafOfModules.naturality_apply e.inv.val
    (homOfLE (show V ≤ ⊤ from le_top)).op (1 : Γ(X,⊤))
  have hm : (SheafOfModules.unit X.ringCatSheaf).val.map
      (homOfLE (show V ≤ ⊤ from le_top)).op (1 : Γ(X,⊤)) = (1 : Γ(X,V)) :=
    map_one (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom
  rw [hm] at h
  exact h.symm

lemma chartFrame_spans_bijective (e : M.restrict i ≅ SheafOfModules.unit X.ringCatSheaf)
    (V : X.Opens) :
    Function.Bijective (fun r : Γ(Y,i ''ᵁ V) =>
      @HSMul.hSMul Γ(Y,i ''ᵁ V) Γ(M,i ''ᵁ V) Γ(M,i ''ᵁ V) inferInstance
        r (M.val.map (homOfLE (i.image_mono (show V ≤ ⊤ from le_top))).op (chartFrame i e))) := by
  let F := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op V)
  let : IsIso (F.map e.inv) := (F.mapIso e).isIso_inv
  have hb : Function.Bijective (fun r : Γ(Y,i ''ᵁ V) =>
      e.inv.val.app (op V) ((i.appIso V).hom r)) :=
    (ConcreteCategory.bijective_of_isIso (F.map e.inv)).comp
      (ConcreteCategory.bijective_of_isIso (i.appIso V).hom)
  have he : (fun r : Γ(Y,i ''ᵁ V) =>
      @HSMul.hSMul Γ(Y,i ''ᵁ V) Γ(M,i ''ᵁ V) Γ(M,i ''ᵁ V) inferInstance
        r (M.val.map (homOfLE (i.image_mono (show V ≤ ⊤ from le_top))).op (chartFrame i e))) =
      (fun r => e.inv.val.app (op V) ((i.appIso V).hom r)) := by
    funext r
    rw [chartFrame_restrict]
    have hl := (e.inv.val.app (op V)).hom.map_smul ((i.appIso V).hom r) (1 : Γ(X,V))
    change e.inv.val.app (op V) (((i.appIso V).hom r : Γ(X,V)) * (1 : Γ(X,V))) =
      (i.appIso V).inv ((i.appIso V).hom r) •
        (e.inv.val.app (op V) (1 : Γ(X,V)) : Γ(M,i ''ᵁ V)) at hl
    rw [mul_one, Iso.hom_inv_id_apply] at hl
    exact hl.symm
  rw [he]
  exact hb

lemma chartFrame_on_open_bijective
    (e : M.restrict i ≅ SheafOfModules.unit X.ringCatSheaf)
    (V : Y.Opens) (hV : V ≤ i ''ᵁ ⊤) :
    Function.Bijective (fun r : Γ(Y,V) =>
      @HSMul.hSMul Γ(Y,V) Γ(M,V) Γ(M,V) inferInstance
        r (M.val.map (homOfLE hV).op (chartFrame i e))) := by
  have he : i ''ᵁ (i ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    apply inf_eq_right.mpr
    simpa only [Scheme.Hom.image_top_eq_opensRange] using hV
  have hb : ∀ h : i ''ᵁ (i ⁻¹ᵁ V) ≤ i ''ᵁ ⊤,
      Function.Bijective (fun r : Γ(Y,i ''ᵁ (i ⁻¹ᵁ V)) =>
        @HSMul.hSMul Γ(Y,i ''ᵁ (i ⁻¹ᵁ V)) Γ(M,i ''ᵁ (i ⁻¹ᵁ V)) Γ(M,i ''ᵁ (i ⁻¹ᵁ V)) inferInstance
          r (M.val.map (homOfLE h).op (chartFrame i e))) :=
    fun _ => chartFrame_spans_bijective i e (i ⁻¹ᵁ V)
  rw [he] at hb
  exact hb hV

lemma chartFrame_isIso (e : M.restrict i ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso (overFromSection M (i ''ᵁ ⊤) (chartFrame i e)) := by
  apply isIso_of_app_bijective
  intro V
  exact chartFrame_on_open_bijective i e V.unop.left (leOfHom V.unop.hom)

end ActualLineFrames


end

end OAI
