import OAI.AlgebraicGeometry.SurfaceCones.DeterminantTransport
import OAI.AlgebraicGeometry.SurfaceCones.CartierEquation

namespace OAI

/-! Exterior powers under change of scalars. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualExterior
universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  (e : A ≃+* B) (M : ModuleCat.{u} A) (n : ℕ)
local instance : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
local instance : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e

/-- Exterior powers commute with transport of the coefficient ring. -/
def changeScalarsEquiv :
    (ModuleCat.restrictScalars e.symm.toRingHom).obj (M.exteriorPower n) ≃ₗ[B]
      ((ModuleCat.restrictScalars e.symm.toRingHom).obj M).exteriorPower n where
  __ := (semilinearEquiv M ((ModuleCat.restrictScalars e.symm.toRingHom).obj M)
    n e (TensorChangeScalars.transportEquiv e M)).toAddEquiv
  map_smul' b x := by
    have h := (semilinearEquiv M ((ModuleCat.restrictScalars e.symm.toRingHom).obj M)
      n e (TensorChangeScalars.transportEquiv e M)).map_smulₛₗ (e.symm b)
        (show M.exteriorPower n from x)
    exact h.trans (congrArg (fun a : B => a •
      (semilinearEquiv M _ n e (TensorChangeScalars.transportEquiv e M)) x)
      (e.apply_symm_apply b))

@[simp] lemma changeScalarsEquiv_mk (z : Fin n → M) :
    changeScalarsEquiv e M n (ModuleCat.exteriorPower.mk (M := M) z) =
      ModuleCat.exteriorPower.mk
        (M := (ModuleCat.restrictScalars e.symm.toRingHom).obj M) z :=
  semilinearMap_mk _ _ _ _ _ _

/-- Checking a map out of a transported exterior power on wedges suffices. -/
lemma changeScalars_hom_ext {P : ModuleCat.{u} B}
    {a b : (ModuleCat.restrictScalars e.symm.toRingHom).obj
      (M.exteriorPower n) ⟶ P}
    (h : ∀ z : Fin n → M, a (ModuleCat.exteriorPower.mk (M := M) z) =
      b (ModuleCat.exteriorPower.mk (M := M) z)) : a = b := by
  have h' : a.hom.comp (TensorChangeScalars.transportEquiv e (M.exteriorPower n)).toLinearMap =
      b.hom.comp (TensorChangeScalars.transportEquiv e (M.exteriorPower n)).toLinearMap :=
    semilinear_ext e.toRingHom M n h
  apply ModuleCat.hom_ext
  ext x
  exact DFunLike.congr_fun h' x

end ActualExterior

end

noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualExterior
universe u v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {R : Cᵒᵖ ⥤ CommRingCat.{u}} {S : Dᵒᵖ ⥤ CommRingCat.{u}}
  (F : D ⥤ C) (e : S ≅ F.op ⋙ R)

local instance (U : Cᵒᵖ) : CommRing ((R ⋙ forget₂ CommRingCat RingCat).obj U) :=
  inferInstanceAs (CommRing (R.obj U))
local instance (V : Dᵒᵖ) : CommRing ((S ⋙ forget₂ CommRingCat RingCat).obj V) :=
  inferInstanceAs (CommRing (S.obj V))

def reindex : PresheafOfModules.{u} (R ⋙ forget₂ _ _) ⥤
    PresheafOfModules.{u} (S ⋙ forget₂ _ _) :=
  PresheafOfModules.pushforward (F := F) (R := R ⋙ forget₂ CommRingCat RingCat)
    (Functor.whiskerRight e.hom (forget₂ CommRingCat RingCat))


/-- A definitionally normalized presentation of restriction, with no second
bundling of the module before taking its exterior power. -/
def reindexObj (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    PresheafOfModules.{u} (S ⋙ forget₂ _ _) where
  obj V := (ModuleCat.restrictScalars (e.symm.app V).commRingCatIsoToRingEquiv.symm.toRingHom).obj (M.obj (F.op.obj V))
  map g := ((reindex F e).obj M).map g
  map_id V := ((reindex F e).obj M).map_id V
  map_comp g h := ((reindex F e).obj M).map_comp g h

def reindexComparison (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (reindex F e).obj M ≅ reindexObj F e M :=
  PresheafOfModules.isoMk (fun V => Iso.refl _)

def reindexPowerIso (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (n : ℕ) (V : Dᵒᵖ) :
    (reindexObj F e (presheaf (R := R) M n)).obj V ≅
      (presheaf (R := S) (reindexObj F e M) n).obj V :=
  (changeScalarsEquiv (e.symm.app V).commRingCatIsoToRingEquiv
    (M.obj (F.op.obj V)) n).toModuleIso

@[simp] lemma reindexObj_map_apply (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    {V W : Dᵒᵖ} (g : V ⟶ W) (z : M.obj (F.op.obj V)) :
    (reindexObj F e M).map g z = M.map (F.op.map g) z := rfl

@[simp] lemma reindexPowerIso_mk (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (n : ℕ)
    (V : Dᵒᵖ) (z : Fin n → M.obj (F.op.obj V)) :
    (reindexPowerIso F e M n V).hom (ModuleCat.exteriorPower.mk z) =
      ModuleCat.exteriorPower.mk (M := (reindexObj F e M).obj V) z :=
  changeScalarsEquiv_mk _ _ _ z

def directReindexIso (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (n : ℕ) :
    reindexObj F e (presheaf (R := R) M n) ≅
      presheaf (R := S) (reindexObj F e M) n :=
  PresheafOfModules.isoMk (reindexPowerIso F e M n)
    (by
      intro V W g
      apply changeScalars_hom_ext (e.symm.app V).commRingCatIsoToRingEquiv
        (M.obj (F.op.obj V)) n
      intro z
      change (reindexPowerIso F e M n W).hom
          (powerMap M n (F.op.map g) (ModuleCat.exteriorPower.mk z)) =
        powerMap (R := S) (reindexObj F e M) n g
          ((reindexPowerIso F e M n V).hom (ModuleCat.exteriorPower.mk z))
      have h₁ := congrArg ((reindexPowerIso F e M n W).hom)
        (powerMap_ι M n (F.op.map g) z)
      have h₂ := reindexPowerIso_mk F e M n W (fun i => M.map (F.op.map g) (z i))
      have h₃ := (powerMap_ι (reindexObj F e M) n g z).symm
      have h₄ := congrArg (fun x : ((reindexObj F e M).obj V).exteriorPower n =>
        powerMap (R := S) (reindexObj F e M) n g x)
          (reindexPowerIso_mk F e M n V z).symm
      exact h₁.trans (h₂.trans (h₃.trans h₄)))

/-- Sectionwise exterior powers commute with coefficient-ring and
open-index isomorphisms, using exactly the standard pushforward functor. -/
def reindexIso (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (n : ℕ) :
    (reindex F e).obj (presheaf (R := R) M n) ≅
      presheaf (R := S) ((reindex F e).obj M) n :=
  reindexComparison F e (presheaf M n) ≪≫ directReindexIso F e M n ≪≫
    (presheafFunctor S n).mapIso (reindexComparison F e M).symm

lemma reindexIso_apply_mk (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (n : ℕ)
    (V : Dᵒᵖ) (z : Fin n → M.obj (F.op.obj V)) :
    (reindexIso F e M n).hom.app V
      (ModuleCat.exteriorPower.mk (M := M.obj (F.op.obj V)) z) =
      ModuleCat.exteriorPower.mk (M := ((reindex F e).obj M).obj V) z := by
  change ModuleCat.exteriorPower.map ((reindexComparison F e M).inv.app V) n
    ((reindexPowerIso F e M n V).hom (ModuleCat.exteriorPower.mk z)) = _
  rw [reindexPowerIso_mk]
  exact (ModuleCat.exteriorPower.map_mk ((reindexComparison F e M).inv.app V) z).trans rfl

end ActualExterior

end

/-! Sheafified exterior powers commute with restriction along open immersions. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualExterior
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

def openRingIso : X.presheaf ≅ f.opensFunctor.op ⋙ Y.presheaf :=
  NatIso.ofComponents (fun V => (f.appIso V.unop).symm)

def openRingHom : X.ringCatSheaf ⟶
    (f.opensFunctor.sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj Y.ringCatSheaf :=
  ⟨Functor.whiskerRight (openRingIso f).hom (forget₂ CommRingCat RingCat)⟩

def openSheafifyMap (P : PresheafOfModules.{u} Y.ringCatSheaf.obj) :
    (schemeSheafification X).obj ((reindex f.opensFunctor (openRingIso f)).obj P) ⟶
      (Scheme.Modules.restrictFunctor f).obj ((schemeSheafification Y).obj P) :=
  ModuleSheafification.comparison f.opensFunctor (openRingHom f) P

instance openSheafifyMap_isIso (P : PresheafOfModules.{u} Y.ringCatSheaf.obj) :
    IsIso (openSheafifyMap f P) :=
  ModuleSheafification.comparison_isIso f.opensFunctor (openRingHom f) P

/-- Sheafified exterior powers commute with open restriction without rank or freeness hypotheses. -/
def openIso (M : Y.Modules) (n : ℕ) :
    ((sheafFunctor Y n).obj M).restrict f ≅
      (sheafFunctor X n).obj (M.restrict f) :=
  letI := openSheafifyMap_isIso f (presheaf M.val n)
  (asIso (openSheafifyMap f (presheaf M.val n))).symm ≪≫
    (schemeSheafification X).mapIso (reindexIso f.opensFunctor (openRingIso f) M.val n)

end ActualExterior

end

/-! Principal-open testing for exterior-sheaf comparisons. -/
noncomputable section
open CategoryTheory Opposite TopologicalSpace
namespace ActualExterior
universe u
variable {X : TopCat.{u}} {ι : Type u} {B : ι → Opens X}
  (hB : Opens.IsBasis (Set.range B))
  {P Q : X.Presheaf AddCommGrpCat.{u}} (a : P ⟶ Q)
  (ha : ∀ i, Function.Bijective (a.app (.op (B i))))

include hB ha in
lemma basis_map_locallyInjective : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) a where
  equalizerSieve_mem {U} s t h := by
    intro x hx
    obtain ⟨_, ⟨_, ⟨i,rfl⟩,rfl⟩, hxi, hiU⟩ := hB.exists_subset_of_mem_open hx U.unop.2
    refine ⟨B i, homOfLE hiU, ?_, hxi⟩
    apply (ha i).1
    have hn := a.naturality (homOfLE hiU).op
    exact (congrArg (fun f => f s) hn).trans ((congrArg
      (Q.map (homOfLE hiU).op) h).trans (congrArg (fun f => f t) hn).symm)

include hB ha in
lemma basis_map_locallySurjective : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) a := by
  apply (TopCat.Presheaf.isLocallySurjective_iff a).2
  intro U t x hx
  obtain ⟨_, ⟨_, ⟨i,rfl⟩,rfl⟩, hxi, hiU⟩ := hB.exists_subset_of_mem_open hx U.2
  exact ⟨B i,hiU,(ha i).2 (Q.map (homOfLE hiU).op t),hxi⟩

include hB ha in
lemma basis_map_W : (Opens.grothendieckTopology X).W a := by
  let := basis_map_locallyInjective hB a ha
  let := basis_map_locallySurjective hB a ha
  exact (Opens.grothendieckTopology X).W_of_isLocallyBijective a

variable {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  {M : PresheafOfModules.{u} R.obj} {N : SheafOfModules.{u} R}
  (φ : M ⟶ N.val)

include hB in
lemma sheafification_map_isIso_of_basis
    (hφ : ∀ i, Function.Bijective (φ.app (.op (B i)))) :
    IsIso ((PresheafOfModules.sheafification (𝟙 R.obj)).map φ) := by
  have hw : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf R.obj).map φ) :=
    basis_map_W hB _ hφ
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (𝟙 R.obj))) φ
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact hw

include hB in
lemma sheafification_lift_isIso_of_basis
    (hφ : ∀ i, Function.Bijective (φ.app (.op (B i)))) :
    IsIso (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv M N).symm φ) := by
  have hm := sheafification_map_isIso_of_basis hB φ hφ
  have hc := NatIso.isIso_app_of_isIso
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit N
  exact CategoryTheory.IsIso.comp_isIso' hm hc
end ActualExterior

end

/-! The exterior sheaf on an affine scheme is associated to the exterior power of its module. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite TopologicalSpace exteriorPower
namespace AffineExterior
universe u
variable (R : Type u) [CommRing R] (M : ModuleCat.{u} R)

local instance (priority := 3000) (U : (Spec (.of R)).Opens) :
    Algebra R Γ(Spec (.of R),U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (.op U)))

local instance (N : (Spec (.of R)).Modules) (U : (Spec (.of R)).Opens) :
    Module Γ(Spec (.of R),U) Γ(N,U) := (N.val.obj (.op U)).isModule
local instance (priority := 2000) (N : (Spec (.of R)).Modules) (U : (Spec (.of R)).Opens) :
    Module R Γ(N,U) :=
  inferInstanceAs (Module R ((modulesSpecToSheaf.obj N).obj.obj (.op U)))
local instance (N : (Spec (.of R)).Modules) (U : (Spec (.of R)).Opens) :
    IsScalarTower R Γ(Spec (.of R),U) Γ(N,U) :=
  IsScalarTower.of_compHom R Γ(Spec (.of R),U) Γ(N,U)
@[reducible] private local instance exteriorBasicOpenAlgebra (r : R) :
    Algebra R Γ(Spec (.of R),PrimeSpectrum.basicOpen r) :=
  inferInstanceAs (Algebra R
    ((Spec.structureSheaf R).obj.obj (.op (PrimeSpectrum.basicOpen r))))

local instance (r : R) : IsLocalization.Away r Γ(Spec (.of R),PrimeSpectrum.basicOpen r) :=
  inferInstanceAs (IsLocalization.Away r
    ((Spec.structureSheaf R).obj.obj (.op (PrimeSpectrum.basicOpen r))))

abbrev E := M.exteriorPower 2
abbrev Ω := (ActualExterior.presheaf (R := (Spec (.of R)).sheaf.obj) (tilde (R := .of R) M).val 2)

local instance (U : (Spec (.of R)).Opens) :
    CommRing ((Spec (.of R)).ringCatSheaf.obj.obj (.op U)) :=
  inferInstanceAs (CommRing ((Spec (.of R)).sheaf.obj.obj (.op U)))
@[reducible] private local instance exteriorTildeSectionModule (N : ModuleCat R)
    (U : (Spec (.of R)).Opens) :
    Module Γ(Spec (.of R),U) ((tilde (R := .of R) N).val.obj (.op U)) :=
  ((tilde (R := .of R) N).val.obj (.op U)).isModule

local instance (N : ModuleCat R) (U : (Spec (.of R)).Opens) :
    Module R ((tilde (R := .of R) N).val.obj (.op U)) :=
  ((modulesSpecToSheaf.obj (tilde (R := .of R) N)).obj.obj (.op U)).isModule
local instance (N : ModuleCat R) (U : (Spec (.of R)).Opens) :
    Module Γ(Spec (.of R),U) ((modulesSpecToSheaf.obj (tilde (R := .of R) N)).obj.obj (.op U)) :=
  ((tilde (R := .of R) N).val.obj (.op U)).isModule
local instance (N : ModuleCat R) (U : (Spec (.of R)).Opens) :
    Module ((Spec (.of R)).ringCatSheaf.obj.obj (.op U)) Γ(tilde (R := .of R) N,U) :=
  ((tilde (R := .of R) N).val.obj (.op U)).isModule
local instance (N : ModuleCat R) (U : (Spec (.of R)).Opens) :
    IsScalarTower R Γ(Spec (.of R),U) ((tilde (R := .of R) N).val.obj (.op U)) :=
  IsScalarTower.of_compHom R Γ(Spec (.of R),U) _
local instance (N : ModuleCat R) (U : (Spec (.of R)).Opens) :
    IsScalarTower R Γ(Spec (.of R),U) ((modulesSpecToSheaf.obj (tilde (R := .of R) N)).obj.obj (.op U)) :=
  IsScalarTower.of_compHom R Γ(Spec (.of R),U) _

local instance (N : ModuleCat R) (r : R) :
    IsLocalizedModule (.powers r) (tilde.toOpen (R := .of R) N (PrimeSpectrum.basicOpen r)).hom :=
  .of_linearEquiv (.powers r) (StructureSheaf.toOpenₗ R N (PrimeSpectrum.basicOpen r))
    ((tilde.modulesSpecToSheafIso (R := .of R) N).app _).toLinearEquiv.symm

local instance (U : (Spec (.of R)).Opens) :
    Algebra R ((Spec (.of R)).ringCatSheaf.obj.obj (.op U)) :=
  inferInstanceAs (Algebra R Γ(Spec (.of R),U))
local instance (Nu : ModuleCat R) (U : (Spec (.of R)).Opens) :
    IsScalarTower R ((Spec (.of R)).ringCatSheaf.obj.obj (.op U))
      ((tilde (R := .of R) Nu).val.obj (.op U)) :=
  IsScalarTower.of_compHom R ((Spec (.of R)).ringCatSheaf.obj.obj (.op U)) _

@[reducible] private local instance exteriorBasicOpenTildeModule (N : ModuleCat R) (r : R) :
    Module Γ(Spec (.of R),PrimeSpectrum.basicOpen r)
      Γ(tilde (R := .of R) N,PrimeSpectrum.basicOpen r) :=
  ((tilde (R := .of R) N).val.obj (.op (PrimeSpectrum.basicOpen r))).isModule

@[reducible] private local instance exteriorTildeUnderlyingRingModule (N : ModuleCat R)
    (U : (Spec (.of R)).Opensᵒᵖ) :
    Module (((Spec (.of R)).sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U)
      ((tilde (R := .of R) N).val.obj U) :=
  ((tilde (R := .of R) N).val.obj U).isModule

@[reducible] private local instance exteriorBasicOpenAssociatedModule (N : ModuleCat R) (r : R) :
    Module Γ(Spec (.of R),PrimeSpectrum.basicOpen r)
      ((modulesSpecToSheaf.obj (tilde (R := .of R) N)).presheaf.obj
        (.op (PrimeSpectrum.basicOpen r))) :=
  ((tilde (R := .of R) N).val.obj (.op (PrimeSpectrum.basicOpen r))).isModule

@[reducible] private local instance exteriorBasicOpenRing (r : R) :
    CommRing ((Spec (.of R)).ringCatSheaf.obj.obj (.op (PrimeSpectrum.basicOpen r))) :=
  inferInstanceAs (CommRing ((Spec (.of R)).sheaf.obj.obj (.op (PrimeSpectrum.basicOpen r))))

@[reducible] private local instance exteriorBasicOpenGammaBaseModule (N : ModuleCat R) (r : R) :
    Module R Γ(tilde (R := .of R) N,PrimeSpectrum.basicOpen r) :=
  ((modulesSpecToSheaf.obj (tilde (R := .of R) N)).obj.obj
    (.op (PrimeSpectrum.basicOpen r))).isModule

private local instance exteriorBasicOpenGammaTower (N : ModuleCat R) (r : R) :
    IsScalarTower R Γ(Spec (.of R),PrimeSpectrum.basicOpen r)
      Γ(tilde (R := .of R) N,PrimeSpectrum.basicOpen r) :=
  IsScalarTower.of_compHom R Γ(Spec (.of R),PrimeSpectrum.basicOpen r) _

@[reducible] private local instance exteriorBasicOpenTildeScalarModule (N : ModuleCat R) (r : R) :
    Module Γ(Spec (.of R),PrimeSpectrum.basicOpen r)
      ((tilde (R := .of R) N).val.obj (.op (PrimeSpectrum.basicOpen r))) :=
  ((tilde (R := .of R) N).val.obj (.op (PrimeSpectrum.basicOpen r))).isModule

@[reducible] private local instance exteriorBasicOpenTildeBaseModule (N : ModuleCat R) (r : R) :
    Module R ((tilde (R := .of R) N).val.obj (.op (PrimeSpectrum.basicOpen r))) :=
  ((modulesSpecToSheaf.obj (tilde (R := .of R) N)).obj.obj
    (.op (PrimeSpectrum.basicOpen r))).isModule

private local instance exteriorBasicOpenTildeTower (N : ModuleCat R) (r : R) :
    IsScalarTower R Γ(Spec (.of R),PrimeSpectrum.basicOpen r)
      ((tilde (R := .of R) N).val.obj (.op (PrimeSpectrum.basicOpen r))) :=
  IsScalarTower.of_compHom R Γ(Spec (.of R),PrimeSpectrum.basicOpen r) _

@[reducible] private local instance exteriorBasicOpenAssociatedBaseModule (N : ModuleCat R)
    (r : R) : Module R ((modulesSpecToSheaf.obj (tilde (R := .of R) N)).presheaf.obj
      (.op (PrimeSpectrum.basicOpen r))) :=
  ((modulesSpecToSheaf.obj (tilde (R := .of R) N)).obj.obj
    (.op (PrimeSpectrum.basicOpen r))).isModule

private local instance exteriorBasicOpenAssociatedTower (N : ModuleCat R) (r : R) :
    IsScalarTower R Γ(Spec (.of R),PrimeSpectrum.basicOpen r)
      ((modulesSpecToSheaf.obj (tilde (R := .of R) N)).presheaf.obj
        (.op (PrimeSpectrum.basicOpen r))) :=
  IsScalarTower.of_compHom R Γ(Spec (.of R),PrimeSpectrum.basicOpen r) _

@[reducible] private local instance exteriorOmegaGammaModule (U : (Spec (.of R)).Opens) :
    Module Γ(Spec (.of R),U) ((Ω R M).obj (.op U)) :=
  ((Ω R M).obj (.op U)).isModule

@[reducible] private local instance exteriorOmegaBasicOpenModule (r : R) :
    Module Γ(Spec (.of R),PrimeSpectrum.basicOpen r)
      ((Ω R M).obj (.op (PrimeSpectrum.basicOpen r))) :=
  ((Ω R M).obj (.op (PrimeSpectrum.basicOpen r))).isModule

@[reducible] private local instance exteriorOmegaRingModule (U : (Spec (.of R)).Opens) :
    Module ((Spec (.of R)).ringCatSheaf.obj.obj (.op U)) ((Ω R M).obj (.op U)) :=
  ((Ω R M).obj (.op U)).isModule

/-- The canonical comparison on each principal open. -/
def basicEquiv (r : R) :
    Γ(tilde (R := .of R) (E R M), PrimeSpectrum.basicOpen r) ≃ₗ[Γ(Spec (.of R),PrimeSpectrum.basicOpen r)]
      ((Ω R M).obj (.op (PrimeSpectrum.basicOpen r))) :=
  by
  let f := (tilde.toOpen (R := .of R) M (PrimeSpectrum.basicOpen r)).hom
  let g := (tilde.toOpen (R := .of R) (E R M) (PrimeSpectrum.basicOpen r)).hom
  have hf : IsLocalizedModule (.powers r) f :=
    tilde.instAwayCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecModuleCatPresheafModulesSheafModulesSpecToSheafOpBasicOpenHomToOpen (R := .of R) M r
  have hg : IsLocalizedModule (.powers r) g :=
    tilde.instAwayCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecModuleCatPresheafModulesSheafModulesSpecToSheafOpBasicOpenHomToOpen (R := .of R) (E R M) r
  exact @ActualExterior.localizationTwoEquiv _ _ _ _ _ (.powers r) _
    _ _ _ _ _ _ _ _ _ _ _ _ _ f hf g hg

/-- Exterior comparison on sections of a principal open. -/
def basicMap (r : R) : (Ω R M).obj (.op (PrimeSpectrum.basicOpen r)) ⟶
    (tilde (R := .of R) (E R M)).val.obj (.op (PrimeSpectrum.basicOpen r)) :=
  ModuleCat.ofHom (X := (Ω R M).obj (.op (PrimeSpectrum.basicOpen r)))
    (Y := (tilde (R := .of R) (E R M)).val.obj (.op (PrimeSpectrum.basicOpen r)))
    (basicEquiv R M r).symm.toLinearMap

@[reducible] private local instance exteriorBasicMapCoe (r : R) :
    CoeFun ((Ω R M).obj (.op (PrimeSpectrum.basicOpen r)) ⟶
      (tilde (R := .of R) (E R M)).val.obj (.op (PrimeSpectrum.basicOpen r)))
      (fun _ => (Ω R M).obj (.op (PrimeSpectrum.basicOpen r)) →
        (tilde (R := .of R) (E R M)).val.obj (.op (PrimeSpectrum.basicOpen r))) :=
  ⟨fun f => f.hom⟩

lemma basicMap_mk (r : R) (z : Fin 2 → M) :
    basicMap R M r (ModuleCat.exteriorPower.mk
      (M := (tilde (R := .of R) M).val.obj (.op (PrimeSpectrum.basicOpen r)))
      (fun i => tilde.toOpen (R := .of R) M (PrimeSpectrum.basicOpen r) (z i))) =
      tilde.toOpen (R := .of R) (E R M) (PrimeSpectrum.basicOpen r) (ModuleCat.exteriorPower.mk (M := M) z) :=
  by
  let := tilde.instAwayCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecModuleCatPresheafModulesSheafModulesSpecToSheafOpBasicOpenHomToOpen (R := .of R) M r
  let := tilde.instAwayCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecModuleCatPresheafModulesSheafModulesSpecToSheafOpBasicOpenHomToOpen (R := .of R) (E R M) r
  exact ActualExterior.localizationTwoInverse_mk (S := Γ(Spec (.of R),PrimeSpectrum.basicOpen r))
    (.powers r) (tilde.toOpen (R := .of R) M (PrimeSpectrum.basicOpen r)).hom
    (tilde.toOpen (R := .of R) (E R M) (PrimeSpectrum.basicOpen r)).hom z

/-- Underlying R-modules of any module presheaf on Spec R. -/
def overBase (P : PresheafOfModules.{u} (Spec (.of R)).ringCatSheaf.obj) :
    (Opens (Spec (.of R)))ᵒᵖ ⥤ ModuleCat.{u} R :=
  (PresheafOfModules.forgetToPresheafModuleCat (.op ⊤)
    (CategoryTheory.Limits.initialOpOfTerminal CategoryTheory.Limits.isTerminalTop)).obj P ⋙
      ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom

local instance (U : (Spec (.of R)).Opens) : Module R ((Ω R M).obj (.op U)) :=
  ((overBase R (Ω R M)).obj (.op U)).isModule
local instance (U : (Spec (.of R)).Opens) :
    IsScalarTower R Γ(Spec (.of R),U) ((Ω R M).obj (.op U)) :=
  IsScalarTower.of_compHom R Γ(Spec (.of R),U) ((Ω R M).obj (.op U))

local instance (U : (Spec (.of R)).Opens) :
    IsScalarTower R ((Spec (.of R)).ringCatSheaf.obj.obj (.op U)) ((Ω R M).obj (.op U)) :=
  IsScalarTower.of_compHom R ((Spec (.of R)).ringCatSheaf.obj.obj (.op U)) _

local instance (U : (Spec (.of R)).Opens) :
    LinearMap.CompatibleSMul ((Ω R M).obj (.op U))
      ((tilde (R := .of R) (E R M)).val.obj (.op U)) R
      (((Spec (.of R)).sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (.op U)) := by
  let : IsScalarTower R Γ(Spec (.of R),U) ((Ω R M).obj (.op U)) :=
    IsScalarTower.of_compHom R Γ(Spec (.of R),U) _
  let : IsScalarTower R Γ(Spec (.of R),U) ((tilde (R := .of R) (E R M)).val.obj (.op U)) :=
    IsScalarTower.of_compHom R Γ(Spec (.of R),U) _
  exact inferInstanceAs (LinearMap.CompatibleSMul ((Ω R M).obj (.op U))
    ((tilde (R := .of R) (E R M)).val.obj (.op U)) R Γ(Spec (.of R),U))

@[reducible] private local instance exteriorOmegaBasicOpenBaseModule (r : R) :
    Module R ((Ω R M).obj (.op (PrimeSpectrum.basicOpen r))) :=
  ((overBase R (Ω R M)).obj (.op (PrimeSpectrum.basicOpen r))).isModule

private local instance exteriorBasicOpenCompatibleSMul (r : R) :
    LinearMap.CompatibleSMul ((Ω R M).obj (.op (PrimeSpectrum.basicOpen r)))
      ((tilde (R := .of R) (E R M)).val.obj (.op (PrimeSpectrum.basicOpen r))) R
      (((Spec (.of R)).sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj
        (.op (PrimeSpectrum.basicOpen r))) := by
  let : IsScalarTower R Γ(Spec (.of R),PrimeSpectrum.basicOpen r)
      ((Ω R M).obj (.op (PrimeSpectrum.basicOpen r))) :=
    IsScalarTower.of_compHom R Γ(Spec (.of R),PrimeSpectrum.basicOpen r) _
  let : IsScalarTower R Γ(Spec (.of R),PrimeSpectrum.basicOpen r)
      ((tilde (R := .of R) (E R M)).val.obj (.op (PrimeSpectrum.basicOpen r))) :=
    IsScalarTower.of_compHom R Γ(Spec (.of R),PrimeSpectrum.basicOpen r) _
  exact inferInstanceAs (LinearMap.CompatibleSMul
    ((Ω R M).obj (.op (PrimeSpectrum.basicOpen r)))
    ((tilde (R := .of R) (E R M)).val.obj (.op (PrimeSpectrum.basicOpen r))) R
    Γ(Spec (.of R),PrimeSpectrum.basicOpen r))

lemma basicMap_natural (r s : R)
    (h : PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen r) (x : (Ω R M).obj (.op (PrimeSpectrum.basicOpen r))) :
    basicMap R M s ((Ω R M).map (homOfLE h).op x) =
      (tilde (R := .of R) (E R M)).val.map (homOfLE h).op (basicMap R M r x) := by
  let f := (tilde.toOpen (R := .of R) M (PrimeSpectrum.basicOpen r)).hom
  let g := (tilde.toOpen (R := .of R) (E R M) (PrimeSpectrum.basicOpen r)).hom
  have hf : IsLocalizedModule (.powers r) f :=
    tilde.instAwayCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecModuleCatPresheafModulesSheafModulesSpecToSheafOpBasicOpenHomToOpen (R := .of R) M r
  have hg : IsLocalizedModule (.powers r) g :=
    tilde.instAwayCarrierCarrierObjOppositeOpensCarrierCarrierCommRingCatSpecModuleCatPresheafModulesSheafModulesSpecToSheafOpBasicOpenHomToOpen (R := .of R) (E R M) r
  let q := ActualExterior.localizationTwoMap (S := Γ(Spec (.of R),PrimeSpectrum.basicOpen r)) f
  let : IsLocalizedModule (.powers r) q :=
    @ActualExterior.localizationTwoMap_isLocalized _ _ _ _ _ (.powers r) _
      _ _ _ _ _ _ _ _ _ _ _ _ _ f hf g hg
  let a := ((basicMap R M s).hom.restrictScalars R).comp
    ((overBase R (Ω R M)).map (homOfLE h).op).hom
  let b := (((modulesSpecToSheaf.obj (tilde (R := .of R) (E R M))).obj.map
    (homOfLE h).op).hom).comp ((basicMap R M r).hom.restrictScalars R)
  have hab : a = b := by
    apply IsLocalizedModule.ext (.powers r) q
      (by
        rintro ⟨_,n,rfl⟩
        rw [map_pow]
        exact ((tilde (R := .of R) (E R M)).isUnit_algebraMap_end_of_le_basicOpen r h).pow n)
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro z
    change basicMap R M s ((Ω R M).map (homOfLE h).op
      (q (ModuleCat.exteriorPower.mk (M := M) z))) =
        (tilde (R := .of R) (E R M)).val.map (homOfLE h).op
          (basicMap R M r (q (ModuleCat.exteriorPower.mk (M := M) z)))
    have hq : q (ModuleCat.exteriorPower.mk (M := M) z) =
        ModuleCat.exteriorPower.mk (M := (tilde (R := .of R) M).val.obj (.op (PrimeSpectrum.basicOpen r)))
          (fun i => tilde.toOpen (R := .of R) M (PrimeSpectrum.basicOpen r) (z i)) :=
      ActualExterior.localizationTwoMap_mk (S := Γ(Spec (.of R),PrimeSpectrum.basicOpen r)) f z
    rw [hq]
    change basicMap R M s (ActualExterior.powerMap (R := (Spec (.of R)).sheaf.obj)
      (tilde (R := .of R) M).val 2 (homOfLE h).op
      (ModuleCat.exteriorPower.mk
        (M := (tilde (R := .of R) M).val.obj (.op (PrimeSpectrum.basicOpen r)))
        (fun i => tilde.toOpen (R := .of R) M (PrimeSpectrum.basicOpen r) (z i)))) = _
    have hp := ActualExterior.powerMap_ι (R := (Spec (.of R)).sheaf.obj)
      (tilde (R := .of R) M).val 2 (homOfLE h).op
      (fun i => tilde.toOpen (R := .of R) M (PrimeSpectrum.basicOpen r) (z i))
    have hp' := congrArg (basicMap R M s).hom hp
    have hs := basicMap_mk R M s z
    have hr := congrArg ((tilde (R := .of R) (E R M)).val.map (homOfLE h).op)
      (basicMap_mk R M r z)
    exact hp'.trans (hs.trans hr.symm)
  exact DFunLike.congr_fun hab x

@[reducible] private local instance exteriorBasicOpensUnderlyingCategory :
    Category.{u} (InducedCategory (Opens (Spec (.of R)))
      (PrimeSpectrum.basicOpen (R := R))) :=
  inferInstanceAs (Category.{u} (InducedCategory (Opens (PrimeSpectrum R))
    (PrimeSpectrum.basicOpen (R := R))))

@[reducible] private local instance exteriorBasicOpensCategory :
    Category.{u} (InducedCategory (Opens (Spec (.of R)))
      (PrimeSpectrum.basicOpen (R := R)))ᵒᵖ :=
  inferInstanceAs (Category.{u} (InducedCategory (Opens (PrimeSpectrum R))
    (PrimeSpectrum.basicOpen (R := R)))ᵒᵖ)

private def basicAdditive :
    (inducedFunctor (fun r : R => (PrimeSpectrum.basicOpen r : (Spec (.of R)).Opens))).op ⋙
        (Ω R M).presheaf ⟶
      (inducedFunctor (fun r : R => (PrimeSpectrum.basicOpen r : (Spec (.of R)).Opens))).op ⋙
        (tilde (R := .of R) (E R M)).presheaf where
  app r := AddCommGrpCat.ofHom (basicMap R M r.unop).hom.toAddMonoidHom
  naturality {r s} i := by
    ext x
    exact basicMap_natural R M r.unop s.unop i.unop.hom.le x

/-- Compatible principal-open comparison, extended by sheaf gluing. -/
def additive : (Ω R M).presheaf ⟶ (tilde (R := .of R) (E R M)).presheaf :=
  TopCat.Sheaf.restrictHomEquivHom _
    ⟨(tilde (R := .of R) (E R M)).presheaf,(tilde (R := .of R) (E R M)).isSheaf⟩
    PrimeSpectrum.isBasis_basic_opens (basicAdditive R M)

lemma additive_basic (r : R) (x : (Ω R M).obj (.op (PrimeSpectrum.basicOpen r))) :
    (additive R M).app (.op (PrimeSpectrum.basicOpen r)) x = basicMap R M r x := by
  let h0 := TopCat.Sheaf.extend_hom_app (Ω R M).presheaf
    ⟨(tilde (R := .of R) (E R M)).presheaf, (tilde (R := .of R) (E R M)).isSheaf⟩
    (B := fun r : R => (PrimeSpectrum.basicOpen r : (Spec (.of R)).Opens))
  let h1 := h0 PrimeSpectrum.isBasis_basic_opens
  let h2 := h1 (basicAdditive R M)
  have h := h2 r
  exact ConcreteCategory.congr_hom h x

lemma additive_res {U V : (Spec (.of R)).Opens} (h : U ≤ V) (x : (Ω R M).obj (.op V)) :
    (additive R M).app (.op U) ((Ω R M).map (homOfLE h).op x) =
      (tilde (R := .of R) (E R M)).val.map (homOfLE h).op ((additive R M).app (.op V) x) :=
  congrArg (fun f => f x) ((additive R M).naturality (homOfLE h).op)

lemma additive_smul (U : (Spec (.of R)).Opens) (t : Γ(Spec (.of R),U))
    (x : (Ω R M).obj (.op U)) :
    (additive R M).app (.op U) (t • x) = t • (additive R M).app (.op U) x := by
  apply TopCat.Presheaf.IsSheaf.section_ext (tilde (R := .of R) (E R M)).isSheaf
  intro p hp
  obtain ⟨_,⟨_,⟨r,rfl⟩,rfl⟩, hpr, hrU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp U.2
  refine ⟨_,hrU,hpr,?_⟩
  change (tilde (R := .of R) (E R M)).val.map (homOfLE hrU).op
    ((additive R M).app (.op U) (t • x)) =
    (tilde (R := .of R) (E R M)).val.map (homOfLE hrU).op
      (t • (additive R M).app (.op U) x)
  have h₁ := additive_res R M (U := PrimeSpectrum.basicOpen r) (V := U) hrU (t • x)
  have h₂ := additive_res R M (U := PrimeSpectrum.basicOpen r) (V := U) hrU x
  refine h₁.symm.trans ?_
  erw [(Ω R M).map_smul, (tilde (R := .of R) (E R M)).val.map_smul, ← h₂]
  erw [additive_basic, additive_basic]
  exact (basicMap R M r).hom.map_smul _ _

/-- Comparison as a morphism over the structure sheaf. -/
def moduleMap : Ω R M ⟶ (tilde (R := .of R) (E R M)).val where
  app U := ModuleCat.ofHom (X := (Ω R M).obj U)
    (Y := (tilde (R := .of R) (E R M)).val.obj U)
    { toFun := (additive R M).app U
      map_add' := ((additive R M).app U).hom.map_add
      map_smul' := additive_smul R M U.unop }
  naturality {U V} i := by
    ext x
    exact congrArg (fun f => f x) ((additive R M).naturality i)

lemma moduleMap_basic_bijective (r : R) :
    Function.Bijective ((moduleMap R M).app (.op (PrimeSpectrum.basicOpen r))) := by
  have he : ⇑((moduleMap R M).app (.op (PrimeSpectrum.basicOpen r))) =
      (basicEquiv R M r).symm := by
    funext x
    change (additive R M).app (.op (PrimeSpectrum.basicOpen r)) x = basicMap R M r x
    exact additive_basic R M r x
  rw [he]
  exact (basicEquiv R M r).symm.bijective

def affineMap : (ActualExterior.sheafFunctor (Spec (.of R)) 2).obj (tilde (R := .of R) M) ⟶
    tilde (R := .of R) (E R M) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (Spec (.of R)).ringCatSheaf.obj)).homEquiv
    (Ω R M) (tilde (R := .of R) (E R M))).symm (moduleMap R M)

instance affineMap_isIso : IsIso (affineMap R M) := by
  change IsIso (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Spec (.of R)).ringCatSheaf.obj)).homEquiv (Ω R M)
      (tilde (R := .of R) (E R M))).symm (moduleMap R M))
  exact ActualExterior.sheafification_lift_isIso_of_basis
    (R := (Spec (.of R)).ringCatSheaf) (M := Ω R M)
    (N := tilde (R := .of R) (E R M)) PrimeSpectrum.isBasis_basic_opens
    (moduleMap R M) (moduleMap_basic_bijective R M)

/-- The intrinsic exterior sheaf on an affine scheme is the tilde of
its exterior module, constructed without local-rank or coherence assumptions. -/
def affineIso : (ActualExterior.sheafFunctor (Spec (.of R)) 2).obj (tilde (R := .of R) M) ≅
    tilde (R := .of R) (E R M) := asIso (affineMap R M)

end AffineExterior

end

/-! The intrinsic canonical sheaf and its local frames on the smooth coefficient charts. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace SourceSymmetry
open ExplicitCone

/-- The intrinsic top exterior power of the cotangent sheaf over the complex field on the source Proj. -/
def canonicalSheaf : projectiveSurface.Modules :=
  (ActualExterior.sheafFunctor projectiveSurface 2).obj
    (ActualCotangent.sheaf projectiveSurfaceToComplex)

/-- The sheaf/module comparison on the twelve smooth coefficient charts. -/
def coefficientCanonicalIso (t : SectionIndex) (ht : Good t) :
    canonicalSheaf.restrict (coefficientIota t ht) ≅
      tilde (R := .of (coefficientChart t))
        ((ActualCotangent.affineModule (k := ℂ) (coefficientChart t)).exteriorPower 2) :=
  ActualExterior.openIso (coefficientIota t ht)
    (ActualCotangent.sheaf projectiveSurfaceToComplex) 2 ≪≫
  (ActualExterior.sheafFunctor (Spec (.of (coefficientChart t))) 2).mapIso
    (coefficientCotangentIso t ht) ≪≫
  AffineExterior.affineIso (coefficientChart t)
    (ActualCotangent.affineModule (k := ℂ) (coefficientChart t))

/-- The canonical line is intrinsically trivial on each coefficient
chart by the explicitly computed top differential. -/
def coefficientCanonicalUnitIso (t : SectionIndex) (ht : Good t) :
    canonicalSheaf.restrict (coefficientIota t ht) ≅
      SheafOfModules.unit (Spec (.of (coefficientChart t))).ringCatSheaf :=
  coefficientCanonicalIso t ht ≪≫
    (tilde.functor (.of (coefficientChart t))).mapIso
      (coefficientCanonicalFrame t ht).toModuleIso ≪≫ tildeSelf

lemma coefficientIota_opensRange (t : SectionIndex) (ht : Good t) :
    (coefficientIota t ht).opensRange = Proj.basicOpen grading (projSection t) := by
  change ((projOpenIso t ht).inv ≫ (Proj.basicOpen grading (projSection t)).ι).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  apply TopologicalSpace.Opens.ext
  exact Scheme.Opens.range_ι _

lemma coefficientIota_cover :
    (⨆ t : {t : SectionIndex // Good t}, (coefficientIota t.val t.property).opensRange) = ⊤ := by
  simp_rw [coefficientIota_opensRange]
  exact smoothOpen_cover

/-- Invertibility is proved for the real intrinsic canonical sheaf by the
chart cover of the source. -/
def canonicalLine : ActualSheafTensor.LineTrivialization projectiveSurface.sheaf canonicalSheaf :=
  ActualSheafTensor.lineTrivializationOfCharts canonicalSheaf
    (fun t : {t : SectionIndex // Good t} => Spec (.of (coefficientChart t.val)))
    (fun t => coefficientIota t.val t.property) coefficientIota_cover
    (fun t => coefficientCanonicalUnitIso t.val t.property)

end SourceSymmetry

end

/-! Coefficient-chart intersections as subrings of the common function field. -/
noncomputable section
namespace FieldPrincipalOpen
variable {k F : Type*} [Field k] [Field F] [Algebra k F]
  (A : Subalgebra k F) [IsFractionRing A F] (d : A) (hd : d ≠ 0)
@[instance_reducible] def overlapAlgebra : Algebra A (away A d hd) := inferInstance
theorem overlapLocalization : IsLocalization.Away d (away A d hd) := inferInstance
theorem overlapTower : IsScalarTower k A (away A d hd) :=
  IsScalarTower.of_algebraMap_eq' rfl
theorem overlapFieldTower : IsScalarTower A (away A d hd) F :=
  IsScalarTower.of_algebraMap_eq' rfl
lemma smooth_away [Algebra.Smooth k A] : Algebra.Smooth k (away A d hd) := by
  let := overlapTower A d hd
  let : Algebra.Etale A (away A d hd) := Algebra.Etale.of_isLocalizationAway d
  exact Algebra.Smooth.comp k A (away A d hd)
end FieldPrincipalOpen
namespace SourceSymmetry
open ExplicitCone

/-- The section ratio determining the overlap in chart `s`. -/
def chartRatio (s t : SectionIndex) : coefficientChart s :=
  ⟨sectionCoefficient t / sectionCoefficient s,
    ratioChart_generator sectionCoefficient s t⟩

lemma chartRatio_ne_zero (s t : SectionIndex) : chartRatio s t ≠ 0 := by
  intro h
  exact div_ne_zero (coefficient_ne_zero t) (coefficient_ne_zero s) (congrArg Subtype.val h)

/-- The common principal open inside the same fixed function field. -/
def coefficientOverlap (s t : SectionIndex) : Subalgebra ℂ L :=
  FieldPrincipalOpen.away (coefficientChart s) (chartRatio s t) (chartRatio_ne_zero s t)

lemma coefficientChart_le_overlap_left (s t : SectionIndex) :
    coefficientChart s ≤ coefficientOverlap s t :=
  FieldPrincipalOpen.le_away _ _ _

lemma coefficientChart_le_overlap_right (s t : SectionIndex) :
    coefficientChart t ≤ coefficientOverlap s t := by
  apply Algebra.adjoin_le
  rintro _ ⟨i,rfl⟩
  have h := (coefficientOverlap s t).mul_mem
    (coefficientChart_le_overlap_left s t (ratioChart_generator sectionCoefficient s i))
    (FieldPrincipalOpen.inv_mem_away (coefficientChart s) (chartRatio s t)
      (chartRatio_ne_zero s t))
  have he : (sectionCoefficient i / sectionCoefficient s) *
      (sectionCoefficient t / sectionCoefficient s)⁻¹ =
      sectionCoefficient i / sectionCoefficient t := by
    field_simp [coefficient_ne_zero]
  change (sectionCoefficient i / sectionCoefficient s) *
    (sectionCoefficient t / sectionCoefficient s)⁻¹ ∈ coefficientOverlap s t at h
  rw [he] at h
  exact h

lemma coefficientOverlap_eq_sup (s t : SectionIndex) :
    coefficientOverlap s t = coefficientChart s ⊔ coefficientChart t := by
  apply le_antisymm
  · apply (FieldPrincipalOpen.away_le_iff _ _ _ _).mpr
    refine ⟨le_sup_left, ?_⟩
    change (sectionCoefficient t / sectionCoefficient s)⁻¹ ∈ _
    rw [inv_div]
    exact (show coefficientChart t ≤ coefficientChart s ⊔ coefficientChart t from le_sup_right)
      (ratioChart_generator sectionCoefficient t s)
  · exact sup_le (coefficientChart_le_overlap_left s t)
      (coefficientChart_le_overlap_right s t)

lemma coefficientOverlap_symm (s t : SectionIndex) :
    coefficientOverlap s t = coefficientOverlap t s := by
  rw [coefficientOverlap_eq_sup, coefficientOverlap_eq_sup, sup_comm]

instance (s t : SectionIndex) : Algebra (coefficientChart s) (coefficientOverlap s t) :=
  FieldPrincipalOpen.overlapAlgebra _ _ _
instance (s t : SectionIndex) : IsLocalization.Away (chartRatio s t) (coefficientOverlap s t) :=
  FieldPrincipalOpen.overlapLocalization _ _ _
lemma coefficientOverlap_smooth (s t : SectionIndex) (hs : Good s) :
    Algebra.Smooth ℂ (coefficientOverlap s t) := by
  let := coefficientChart_smooth s hs
  exact FieldPrincipalOpen.smooth_away (coefficientChart s) (chartRatio s t)
    (chartRatio_ne_zero s t)

end SourceSymmetry


/-! Functoriality of top differential modules under chart localization. -/
open Module KaehlerDifferential
namespace CanonicalCoordinates

variable {R S M N I : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S M]
  [Module R N] [Module S N] [IsScalarTower R S M] [IsScalarTower R S N]

def alternatingRestrictScalars (f : AlternatingMap S M N I) : AlternatingMap R M N I where
  toMultilinearMap := f.toMultilinearMap.restrictScalars R
  map_eq_zero_of_eq' := f.map_eq_zero_of_eq

variable (k A B : Type*) [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

local instance : Module A Ω[A⁄k] := kaehlerModule k A
local instance : Module B Ω[B⁄k] := kaehlerModule k B
local instance : Module A (⋀[A]^2 Ω[A⁄k]) := topModule _ _
local instance : Module B (⋀[B]^2 Ω[B⁄k]) := topModule _ _
local instance : SMul A (⋀[A]^2 Ω[A⁄k]) := (topModule _ _).toSMul
local instance : SMul B (⋀[B]^2 Ω[B⁄k]) := (topModule _ _).toSMul

/-- The canonical map on the second exterior power of differentials. -/
def topDifferentialMap : (⋀[A]^2 Ω[A⁄k]) →ₗ[A] (⋀[B]^2 Ω[B⁄k]) :=
  exteriorPower.alternatingMapLinearEquiv
    ((alternatingRestrictScalars (R := A) (exteriorPower.ιMulti B 2)).compLinearMap
      (KaehlerDifferential.map k k A B))

lemma topDifferentialMap_volume (a : Fin 2 → A) :
    topDifferentialMap k A B (exteriorPower.ιMulti A 2 (fun i => D k A (a i))) =
      exteriorPower.ιMulti B 2 (fun i => D k B (algebraMap A B (a i))) := by
  simp only [topDifferentialMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  change exteriorPower.ιMulti B 2 (fun i => KaehlerDifferential.map k k A B (D k A (a i))) = _
  simp only [KaehlerDifferential.map_D]

lemma topDifferentialMap_coe (m : ⋀[A]^2 Ω[A⁄k]) :
    (topDifferentialMap k A B m : ExteriorAlgebra B Ω[B⁄k]) =
      exteriorMap k A B (m : ExteriorAlgebra A Ω[A⁄k]) := by
  let f : (⋀[A]^2 Ω[A⁄k]) →ₗ[A] ExteriorAlgebra B Ω[B⁄k] :=
    ((Submodule.subtype (⋀[B]^2 Ω[B⁄k])).restrictScalars A).comp (topDifferentialMap k A B)
  let g : (⋀[A]^2 Ω[A⁄k]) →ₗ[A] ExteriorAlgebra B Ω[B⁄k] := determinantMap k A B
  have h : f = g := by
    apply Submodule.linearMap_eq_iff_of_span_eq_top _ _
      (exteriorPower.ιMulti_span_of_span A 2 Ω[A⁄k] (KaehlerDifferential.span_range_derivation k A)) |>.mpr
    rintro ⟨_,⟨u,hu,rfl⟩⟩
    choose a ha using fun i => hu (Set.mem_range_self i)
    have hu' : u = fun i => D k A (a i) := funext (fun i => (ha i).symm)
    change f (exteriorPower.ιMulti A 2 u) = g (exteriorPower.ιMulti A 2 u)
    rw [hu']
    change (topDifferentialMap k A B (exteriorPower.ιMulti A 2 (fun i => D k A (a i))) :
      ExteriorAlgebra B Ω[B⁄k]) = _
    rw [topDifferentialMap_volume]
    simp only [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]
    exact (determinantMap_volume k A B a).symm
  exact DFunLike.congr_fun h m

variable (F : Type*) [CommRing F] [Algebra k F] [Algebra A F] [Algebra B F]
  [IsScalarTower k A F] [IsScalarTower k B F] [IsScalarTower A B F]

lemma determinantMap_natural (m : ⋀[A]^2 Ω[A⁄k]) :
    determinantMap k B F (topDifferentialMap k A B m) = determinantMap k A F m := by
  let f := ((determinantMap k B F).restrictScalars A).comp (topDifferentialMap k A B)
  have h : f = determinantMap k A F := by
    apply Submodule.linearMap_eq_iff_of_span_eq_top _ _
      (exteriorPower.ιMulti_span_of_span A 2 Ω[A⁄k] (KaehlerDifferential.span_range_derivation k A)) |>.mpr
    rintro ⟨_,⟨u,hu,rfl⟩⟩
    choose a ha using fun i => hu (Set.mem_range_self i)
    have hu' : u = fun i => D k A (a i) := funext (fun i => (ha i).symm)
    change f (exteriorPower.ιMulti A 2 u) = determinantMap k A F (exteriorPower.ιMulti A 2 u)
    rw [hu']
    change determinantMap k B F (topDifferentialMap k A B
      (exteriorPower.ιMulti A 2 (fun i => D k A (a i)))) = _
    rw [topDifferentialMap_volume, determinantMap_volume, determinantMap_volume]
    simp only [IsScalarTower.algebraMap_apply A B F]
  exact DFunLike.congr_fun h m

end CanonicalCoordinates

end

/-! Restriction of top differential sections to chart overlaps. -/
noncomputable section
open Module KaehlerDifferential CanonicalCoordinates
open scoped nonZeroDivisors
namespace Subalgebra
open scoped _root_.Subalgebra
variable {k F : Type*} [CommRing k] [Field F] [Algebra k F]
  (A B : Subalgebra k F) (h : A ≤ B)
@[instance_reducible] def inclusionAlgebra : Algebra A B :=
  (Subalgebra.inclusion h).toRingHom.toAlgebra
theorem inclusionTower :
    letI := inclusionAlgebra A B h
    IsScalarTower k A B := by
  let := inclusionAlgebra A B h
  exact IsScalarTower.of_algebraMap_eq' rfl
theorem inclusionFieldTower :
    letI := inclusionAlgebra A B h
    IsScalarTower A B F := by
  let := inclusionAlgebra A B h
  exact IsScalarTower.of_algebraMap_eq' rfl
include h in
lemma isFractionRing_of_le [IsFractionRing A F] : IsFractionRing B F := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a,b,hb,hz⟩ := IsFractionRing.div_surjective A z
  exact ⟨Subalgebra.inclusion h a, Subalgebra.inclusion h b, hz.symm⟩
end Subalgebra

namespace CanonicalCoordinates
variable {k F : Type*} [CommRing k] [Field F] [Algebra k F]
  (A B : Subalgebra k F) (h : A ≤ B)

local instance (D : Subalgebra k F) : Module D Ω[D⁄k] := kaehlerModule k D
local instance (D : Subalgebra k F) : Module D (⋀[D]^2 Ω[D⁄k]) := topModule _ _
local instance (D : Subalgebra k F) : SMul D (⋀[D]^2 Ω[D⁄k]) := (topModule _ _).toSMul

/-- restriction along an inclusion of affine coordinate subrings. -/
def topInclusion : (⋀[A]^2 Ω[A⁄k]) →ₗ[k] (⋀[B]^2 Ω[B⁄k]) := by
  letI := Subalgebra.inclusionAlgebra A B h
  letI := Subalgebra.inclusionTower A B h
  exact (topDifferentialMap k A B).restrictScalars k

lemma topInclusion_natural (m : ⋀[A]^2 Ω[A⁄k]) :
    determinantMap k B F (topInclusion A B h m) = determinantMap k A F m := by
  let := Subalgebra.inclusionAlgebra A B h
  let := Subalgebra.inclusionTower A B h
  let := Subalgebra.inclusionFieldTower A B h
  exact determinantMap_natural k A B F m

variable (C : Subalgebra k F) (hAC : A ≤ C) (hBC : B ≤ C)
  [Algebra.FormallySmooth k C] [IsFractionRing C F] [Invertible (2 : C)]

lemma topInclusion_eq_smul_of_rational
    (a : ⋀[A]^2 Ω[A⁄k]) (b : ⋀[B]^2 Ω[B⁄k]) (u : C)
    (he : determinantMap k A F a = (u : F) • determinantMap k B F b) :
    topInclusion A C hAC a = u • topInclusion B C hBC b := by
  let : Algebra.FormallyEtale C F := Algebra.FormallyEtale.of_isLocalization C⁰
  apply determinantMap_injective k C F
  rw [map_smul, topInclusion_natural, topInclusion_natural]
  exact he.trans (IsScalarTower.algebraMap_smul F u (determinantMap k B F b))

end CanonicalCoordinates


end

/-! Weight-five transition equations for the canonical differential sections. -/
noncomputable section
open Module KaehlerDifferential CanonicalCoordinates
open scoped nonZeroDivisors
namespace CanonicalCoordinates
@[instance_reducible] def invertibleTwo (k A : Type*) [Field k] [CharZero k]
    [CommRing A] [Algebra k A] : Invertible (2 : A) := by
  have h : IsUnit (2 : k) := isUnit_iff_ne_zero.mpr (by norm_num)
  have h' : IsUnit (2 : A) := by simpa only [map_ofNat] using h.map (algebraMap k A)
  exact h'.invertible
end CanonicalCoordinates
namespace SourceSymmetry
open ExplicitCone
local instance (A : Subalgebra ℂ L) : Module A Ω[A⁄ℂ] := kaehlerModule ℂ A
local instance (A : Subalgebra ℂ L) : Module A (⋀[A]^2 Ω[A⁄ℂ]) := topModule _ _
local instance (A : Subalgebra ℂ L) : SMul A (⋀[A]^2 Ω[A⁄ℂ]) := (topModule _ _).toSMul
local instance : Module L Ω[L⁄ℂ] := kaehlerModule ℂ L
local instance : Module L (ExteriorAlgebra L Ω[L⁄ℂ]) := canonicalExteriorModule _ _
local instance : SMul L (ExteriorAlgebra L Ω[L⁄ℂ]) := exteriorSMul _ _
local instance : MulAction L (ExteriorAlgebra L Ω[L⁄ℂ]) := exteriorMulAction _ _
local instance : Algebra L (ExteriorAlgebra L Ω[L⁄ℂ]) := rationalExteriorAlgebra _ _
local instance (A : Subalgebra ℂ L) : IsScalarTower A L (ExteriorAlgebra L Ω[L⁄ℂ]) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl
local instance (A : Subalgebra ℂ L) : Module A A := selfModule A
local instance (A : Subalgebra ℂ L) : IsDomain A := subalgebraDomain ℂ L A
local instance (A : Subalgebra ℂ L) : IsScalarTower ℂ A L := subalgebraTower ℂ L A
local instance (A : Subalgebra ℂ L) : FaithfulSMul A L := subalgebraFaithful ℂ L A
local instance (A : Subalgebra ℂ L) : Invertible (2 : A) := invertibleTwo ℂ A

instance (s t : SectionIndex) : IsFractionRing (coefficientOverlap s t) L :=
  Subalgebra.isFractionRing_of_le (coefficientChart s) (coefficientOverlap s t)
    (coefficientChart_le_overlap_left s t)

/-- The transition value is an element of the intersection ring. -/
def canonicalOverlapRatio (s t : SectionIndex) : coefficientOverlap s t :=
  ⟨(sectionCoefficient s / sectionCoefficient t)^5,
    (coefficientOverlap s t).pow_mem
      (coefficientChart_le_overlap_right s t
        (ratioChart_generator sectionCoefficient t s)) 5⟩

/-- Restriction of top forms along an inclusion of coefficient rings. -/
def coefficientTopInclusion (A B : Subalgebra ℂ L) (h : A ≤ B)
    (m : ⋀[A]^2 Ω[A⁄ℂ]) : ⋀[B]^2 Ω[B⁄ℂ] := by
  let hKA : Algebra ℂ A := inferInstance
  let hKB : Algebra ℂ B := inferInstance
  letI hAB : Algebra A B := (Subalgebra.inclusion h).toRingHom.toAlgebra
  letI : Algebra ℂ A := hKA
  letI : Algebra ℂ B := hKB
  letI : SMul ℂ A := hKA.toSMul
  letI : SMul A B := hAB.toSMul
  letI : SMul ℂ B := hKB.toSMul
  letI hT : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq' rfl
  exact @topDifferentialMap ℂ A B Complex.commRing
    (inferInstanceAs (CommRing A)) (inferInstanceAs (CommRing B))
    hKA hKB hAB hT m

/-- Restriction to an included affine ring preserves the associated rational top form. -/
lemma coefficientTopInclusion_natural (A B : Subalgebra ℂ L) (h : A ≤ B)
    (m : ⋀[A]^2 Ω[A⁄ℂ]) :
    determinantMap ℂ B L (coefficientTopInclusion A B h m) = determinantMap ℂ A L m := by
  let hKA : Algebra ℂ A := inferInstance
  let hKB : Algebra ℂ B := inferInstance
  let hAB : Algebra A B := (Subalgebra.inclusion h).toRingHom.toAlgebra
  let : Algebra ℂ A := hKA
  let : Algebra ℂ B := hKB
  let : SMul ℂ A := hKA.toSMul
  let : SMul A B := hAB.toSMul
  let : SMul ℂ B := hKB.toSMul
  let hT : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq' rfl
  exact determinantMap_natural ℂ A B L m

/-- Equality in the top differential module of the common open.
Together with the frames, this is the canonical line's weight-five transition. -/
lemma canonical_overlap_transition (s t : SectionIndex) (hs : Good s) (ht : Good t) :
    coefficientTopInclusion (coefficientChart s) (coefficientOverlap s t)
        (coefficientChart_le_overlap_left s t) (coefficientCanonicalGenerator s hs) =
      canonicalOverlapRatio s t •
      coefficientTopInclusion (coefficientChart t) (coefficientOverlap s t)
        (coefficientChart_le_overlap_right s t) (coefficientCanonicalGenerator t ht) := by
  let := coefficientOverlap_smooth s t hs
  let : Algebra.FormallyEtale (coefficientOverlap s t) L :=
    Algebra.FormallyEtale.of_isLocalization (coefficientOverlap s t)⁰
  apply determinantMap_injective ℂ (coefficientOverlap s t) L
  have hleft := coefficientTopInclusion_natural (coefficientChart s) (coefficientOverlap s t)
    (coefficientChart_le_overlap_left s t) (coefficientCanonicalGenerator s hs)
  have hright := coefficientTopInclusion_natural (coefficientChart t) (coefficientOverlap s t)
    (coefficientChart_le_overlap_right s t) (coefficientCanonicalGenerator t ht)
  have hratio := coefficientCanonicalGenerator_transition s t hs ht
  have hscalar := IsScalarTower.algebraMap_smul L (canonicalOverlapRatio s t)
    (determinantMap ℂ (coefficientChart t) L (coefficientCanonicalGenerator t ht))
  have hmul := (determinantMap ℂ (coefficientOverlap s t) L).map_smul
    (canonicalOverlapRatio s t)
    (coefficientTopInclusion (coefficientChart t) (coefficientOverlap s t)
      (coefficientChart_le_overlap_right s t) (coefficientCanonicalGenerator t ht))
  exact hleft.trans (hratio.trans (hscalar.trans
    ((congrArg (fun v => canonicalOverlapRatio s t • v) hright.symm).trans hmul.symm)))

end SourceSymmetry

end

end OAI
