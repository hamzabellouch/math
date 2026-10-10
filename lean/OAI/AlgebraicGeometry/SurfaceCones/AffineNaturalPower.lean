import OAI.AlgebraicGeometry.SurfaceCones.CartierImageFiltration

namespace OAI

/-!
# Principal equations and restriction of tensor powers

This development accompanies *A Complete Local Domain without a Small
Cohen–Macaulay Module* (OpenAI, 2026).
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
open Scheme.Modules
namespace AffineNaturalScalar
variable (R : CommRingCat.{0}) (b : 𝟭 (Spec R).Modules ⟶ 𝟭 (Spec R).Modules)
/-- The scalar formula for powers of a natural action on an associated sheaf. -/
lemma power_eq (M : ModuleCat R) (n : ℕ) :
    (End.of (b.app (tilde M)) ^ n).asHom = (tilde.functor R).map
      (ModuleCat.ofHom (scalar R b ^ n • (LinearMap.id : M →ₗ[R] M))) := by
  let F := tilde.functor R
  let a : End M := End.of (F.preimage (b.app (tilde M)))
  have ha : ∀ (k : ℕ) (m : M), (a ^ k).asHom m = scalar R b ^ k • m := by
    intro k
    induction k with
    | zero => intro m; simp [End.asHom, End.one_def]
    | succ k ih =>
      intro m
      rw [pow_succ', End.mul_def]
      change a.asHom ((a ^ k).asHom m) = _
      rw [ih]
      change F.preimage (b.app (tilde M)) (scalar R b ^ k • m) = _
      rw [preimage_apply, ← mul_smul, ← pow_succ']
  have hn : (a ^ n).asHom =
      ModuleCat.ofHom (scalar R b ^ n • (LinearMap.id : M →ₗ[R] M)) := by
    apply ModuleCat.hom_ext
    ext m
    exact ha n m
  change (End.of (b.app (F.obj M)) ^ n).asHom = _
  have hf : End.of (b.app (F.obj M)) = (Functor.mapEnd M F) a := by
    exact (F.map_preimage (b.app (tilde M))).symm
  calc
    (End.of (b.app (F.obj M)) ^ n).asHom = ((Functor.mapEnd M F) a ^ n).asHom :=
      congrArg (fun z : End (F.obj M) => (z ^ n).asHom) hf
    _ = ((Functor.mapEnd M F) (a ^ n)).asHom :=
      congrArg End.asHom ((Functor.mapEnd M F).map_pow a n).symm
    _ = F.map ((a ^ n).asHom) := rfl
    _ = _ := congrArg F.map hn
end AffineNaturalScalar

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CartierImageFiltration
universe u v
variable {C : Type u} [Category.{v} C]
  (T : C ⥤ C) (e : T ≅ 𝟭 C)

/-- The iterated tensor power trivialization, derived from the given
line trivialization, retaining its compatibility with the ideal action. -/
def trivialPowerIso (n : ℕ) (M : C) : (power T n).obj M ≅ M :=
  powerComparison T (𝟭 C) (𝟭 C)
    (Functor.rightUnitor T ≪≫ e ≪≫ (Functor.leftUnitor (𝟭 C)).symm) n M ≪≫
    identityPowerIso n M

lemma trivialPowerIso_action (a : T ⟶ 𝟭 C) (n : ℕ) (M : C) :
    (trivialPowerIso T e n M).hom ≫ (End.of ((e.inv ≫ a).app M) ^ n).asHom =
      (powerAction T a n).app M := by
  let cmp : T ⋙ 𝟭 C ≅ 𝟭 C ⋙ 𝟭 C :=
    Functor.rightUnitor T ≪≫ e ≪≫ (Functor.leftUnitor (𝟭 C)).symm
  have hh (N : C) : (cmp.app N).hom ≫ (e.inv ≫ a).app ((𝟭 C).obj N) =
      (𝟭 C).map (a.app N) := by simp [cmp]
  have h := powerComparison_action T (𝟭 C) (𝟭 C) cmp a (e.inv ≫ a) hh n M
  simpa only [trivialPowerIso, Iso.trans_hom, Category.assoc, powerAction_id,
    Functor.id_map, Functor.id_obj] using h
end CartierImageFiltration

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
open Scheme.Modules ActualSheafTensor CartierImageFiltration
namespace CartierAffineLattice
variable {R : CommRingCat.{0}}

private lemma natural_power_intertwine {C : Type*} [Category C]
    (b : 𝟭 C ⟶ 𝟭 C) {M N : C} (f : M ⟶ N) (n : ℕ) :
    f ≫ (End.of (b.app N) ^ n).asHom = (End.of (b.app M) ^ n).asHom ≫ f := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', End.mul_def, End.asHom, Category.assoc]
    rw [← Category.assoc, ih, Category.assoc]
    exact congrArg ((End.of (b.app M) ^ n).asHom ≫ ·) (b.naturality f)

/-- The natural scalar power on every quasi-coherent affine sheaf,
transported via its canonical affine presentation. -/
lemma natural_coherent_power (b : 𝟭 (Spec R).Modules ⟶ 𝟭 (Spec R).Modules)
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    (End.of (b.app M) ^ n).asHom = affineScalar (AffineNaturalScalar.scalar R b ^ n) M := by
  let P := moduleSpecΓFunctor.obj M
  let c := affineCounitIso M
  have h := natural_power_intertwine b c.hom n
  apply (cancel_epi c.hom).mp
  change c.hom ≫ (End.of (b.app M) ^ n).asHom =
    c.hom ≫ c.inv ≫ tildeScalar (AffineNaturalScalar.scalar R b ^ n) P ≫ c.hom
  rw [c.hom_inv_id_assoc]
  exact h.trans (congrArg (· ≫ c.hom) (AffineNaturalScalar.power_eq R b P n))

/-- Exact comparison between the ideal tensor power and its principal equation on a trivializing affine Cartier chart. -/
lemma trivial_power_scalar (L : (Spec R).Modules)
    (eL : L ≅ SheafOfModules.unit (Spec R).ringCatSheaf)
    (i : L ⟶ SheafOfModules.unit (Spec R).ringCatSheaf)
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    (trivialPowerIso (tensorLeft (Spec R).sheaf L)
      (trivialTensorIso (Spec R).sheaf eL) n M).hom ≫
      affineScalar (AffineCartierNilpotence.equation L eL i ^ n) M =
      (powerAction (tensorLeft (Spec R).sheaf L) (idealAction (Spec R).sheaf i) n).app M := by
  have h := trivialPowerIso_action (tensorLeft (Spec R).sheaf L)
    (trivialTensorIso (Spec R).sheaf eL) (idealAction (Spec R).sheaf i) n M
  erw [natural_coherent_power, AffineCartierNilpotence.normalized_scalar] at h
  exact h
end CartierAffineLattice

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
open Scheme.Modules ActualSheafTensor CartierImageFiltration
namespace CartierAffineLattice
variable {R : CommRingCat.{0}}

private local instance affineSheafSectionModule (M : (Spec R).Modules)
    (U : (Spec R).Opensᵒᵖ) : Module ((Spec R).sheaf.obj.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule

private local instance affineFiniteQuasicoherent (M : (Spec R).Modules)
    [M.IsFinitePresentation] : M.IsQuasicoherent :=
  (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent

/-- The affine Cartier lattice extension uses iterated tensor powers of the ideal.
Its two injections restrict to the prescribed identification times the Cartier action. -/
lemma exists_twisted_coherent_sandwich [IsNoetherianRing R]
    (L : (Spec R).Modules) (eL : L ≅ SheafOfModules.unit (Spec R).ringCatSheaf)
    (i : L ⟶ SheafOfModules.unit (Spec R).ringCatSheaf) [Mono i]
    (M N : (Spec R).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : ∀ U, Module.IsTorsionFree ((Spec R).sheaf.obj.obj U) (M.val.obj U))
    (hN : ∀ U, Module.IsTorsionFree ((Spec R).sheaf.obj.obj U) (N.val.obj U))
    (e : M.over (PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation L eL i)) ≅
      N.over (PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation L eL i))) :
    let U := PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation L eL i)
    let T := tensorLeft (Spec R).sheaf L
    let act := idealAction (Spec R).sheaf i
    ∃ (n : ℕ) (a : (power T n).obj M ⟶ N) (b : (power T n).obj N ⟶ M),
      Mono a ∧ Mono b ∧
      a.over U = ((powerAction T act n).app M).over U ≫ e.hom ∧
      b.over U = ((powerAction T act n).app N).over U ≫ e.inv := by
  let t := AffineCartierNilpotence.equation L eL i
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen t
  let T := tensorLeft (Spec R).sheaf L
  let act := idealAction (Spec R).sheaf i
  obtain ⟨n, a, b, ha, hb, haf, hbf, _, _⟩ :=
    exists_coherent_sheaf_sandwich L eL i M N hM hN e
  change (SheafOfModules.overFunctor (Spec R).ringCatSheaf U).map a =
    (SheafOfModules.overFunctor (Spec R).ringCatSheaf U).map (affineScalar (t ^ n) M) ≫ e.hom at haf
  change (SheafOfModules.overFunctor (Spec R).ringCatSheaf U).map b =
    (SheafOfModules.overFunctor (Spec R).ringCatSheaf U).map (affineScalar (t ^ n) N) ≫ e.inv at hbf
  let cM := trivialPowerIso T (trivialTensorIso (Spec R).sheaf eL) n M
  let cN := trivialPowerIso T (trivialTensorIso (Spec R).sheaf eL) n N
  have : Mono a := ha
  have : Mono b := hb
  refine ⟨n, cM.hom ≫ a, cN.hom ≫ b,
    mono_comp' (@IsIso.mono_of_iso _ _ _ _ _ cM.isIso_hom) ha,
    mono_comp' (@IsIso.mono_of_iso _ _ _ _ _ cN.isIso_hom) hb, ?_, ?_⟩
  · change (SheafOfModules.overFunctor (Spec R).ringCatSheaf U).map (cM.hom ≫ a) = _
    erw [Functor.map_comp, haf, ← Category.assoc, ← Functor.map_comp]
    exact congrArg (· ≫ e.hom)
      (congrArg (SheafOfModules.overFunctor (Spec R).ringCatSheaf U).map
        (trivial_power_scalar L eL i M n))
  · change (SheafOfModules.overFunctor (Spec R).ringCatSheaf U).map (cN.hom ≫ b) = _
    erw [Functor.map_comp, hbf, ← Category.assoc, ← Functor.map_comp]
    exact congrArg (· ≫ e.inv)
      (congrArg (SheafOfModules.overFunctor (Spec R).ringCatSheaf U).map
        (trivial_power_scalar L eL i N n))
end CartierAffineLattice

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CartierImageFiltration
universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (T : C ⥤ C) (a : T ⟶ 𝟭 C)

instance power_preservesMonos [T.PreservesMonomorphisms] (n : ℕ) :
    (power T n).PreservesMonomorphisms := by
  induction n with
  | zero => exact inferInstanceAs ((𝟭 C).PreservesMonomorphisms)
  | succ n ih => exact inferInstanceAs ((T ⋙ power T n).PreservesMonomorphisms)

/-- Once a pole is cleared, every larger ideal twist is cleared.
The extending maps remain monomorphisms and retain their prescribed
restriction; this is the uniform-exponent step in finite-cover gluing. -/
lemma exists_extension_of_le [T.PreservesMonomorphisms]
    (F : C ⥤ D) (M N : C) [Mono (a.app M)]
    (e : F.obj M ⟶ F.obj N) {n m : ℕ} (hnm : n ≤ m)
    (z : (power T n).obj M ⟶ N) [Mono z]
    (hz : F.map z = F.map ((powerAction T a n).app M) ≫ e) :
    ∃ w : (power T m).obj M ⟶ N, Mono w ∧
      F.map w = F.map ((powerAction T a m).app M) ≫ e := by
  induction m, hnm using Nat.le_induction with
  | base => exact ⟨z, inferInstance, hz⟩
  | succ m _ ih =>
    change ∃ w : (power T m).obj (T.obj M) ⟶ N, Mono w ∧
      F.map w = F.map ((powerAction T a m).app (T.obj M) ≫ a.app M) ≫ e
    obtain ⟨w, hw, he⟩ := ih
    have : Mono w := hw
    refine ⟨(power T m).map (a.app M) ≫ w, inferInstance, ?_⟩
    rw [F.map_comp, he, ← Category.assoc, ← F.map_comp]
    have h := (powerAction T a m).naturality (a.app M)
    simp only [Functor.id_map, Functor.id_obj] at h
    exact congrArg (fun q => F.map q ≫ e) h

end CartierImageFiltration

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
open Scheme.Modules ActualSheafTensor CartierImageFiltration
namespace CartierAffineLattice
variable {R : CommRingCat.{0}}

attribute [local instance] affineSheafSectionModule affineFiniteQuasicoherent

/-- A coherent lattice identification on an affine Cartier puncture
extends injectively after every sufficiently large ideal twist, in
both directions with one common lower bound. This is exactly the uniform
local extension needed to choose one exponent on a finite trivializing cover. -/
lemma exists_uniform_twisted_sandwich [IsNoetherianRing R]
    (L : (Spec R).Modules) (eL : L ≅ SheafOfModules.unit (Spec R).ringCatSheaf)
    (i : L ⟶ SheafOfModules.unit (Spec R).ringCatSheaf) [Mono i]
    (M N : (Spec R).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : ∀ U, Module.IsTorsionFree ((Spec R).sheaf.obj.obj U) (M.val.obj U))
    (hN : ∀ U, Module.IsTorsionFree ((Spec R).sheaf.obj.obj U) (N.val.obj U))
    (e : M.over (PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation L eL i)) ≅
      N.over (PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation L eL i))) :
    let U := PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation L eL i)
    let T := tensorLeft (Spec R).sheaf L
    let act := idealAction (Spec R).sheaf i
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ (a : (power T n).obj M ⟶ N) (b : (power T n).obj N ⟶ M),
        Mono a ∧ Mono b ∧
        a.over U = ((powerAction T act n).app M).over U ≫ e.hom ∧
        b.over U = ((powerAction T act n).app N).over U ≫ e.inv := by
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation L eL i)
  let T := tensorLeft (Spec R).sheaf L
  let act := idealAction (Spec R).sheaf i
  let F := SheafOfModules.overFunctor (Spec R).ringCatSheaf U
  have : T.PreservesMonomorphisms := tensorLeft_preservesMonomorphisms_of_unitIso _ L eL
  have : Mono (act.app M) := @idealAction_mono_of_unitIso _ _ _ (Spec R).sheaf _ _ L i ‹Mono i› eL M hM
  have : Mono (act.app N) := @idealAction_mono_of_unitIso _ _ _ (Spec R).sheaf _ _ L i ‹Mono i› eL N hN
  obtain ⟨k, a, b, ha, hb, hae, hbe⟩ := exists_twisted_coherent_sandwich L eL i M N hM hN e
  have : Mono a := ha
  have : Mono b := hb
  refine ⟨k, fun n hn => ?_⟩
  obtain ⟨a', ha', hae'⟩ := exists_extension_of_le T act F M N e.hom hn a hae
  obtain ⟨b', hb', hbe'⟩ := exists_extension_of_le T act F N M e.inv hn b hbe
  exact ⟨a', b', ha', hb', hae', hbe'⟩
end CartierAffineLattice

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)
    (e : SectionTrivialization f U)

/-- The nonvanishing locus of the equation of a Cartier ideal avoids the closed divisor. -/
lemma equation_basicOpen_disjoint :
    f ⁻¹ᵁ Y.basicOpen (equation f U e) = ⊥ := by
  rw [Scheme.preimage_basicOpen]
  have hz : f.app U (equation f U e) = 0 := equation_mem_kernel f U e
  rw [hz, Scheme.basicOpen_zero]

/-- The same statement on the canonical affine chart, with precisely the
ordinary principal open used by associated-module localization. -/
lemma equation_affineChart_disjoint (hU : IsAffineOpen U) :
    f ⁻¹ᵁ (hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen (equation f U e)) = ⊥ := by
  rw [IsAffineOpen.fromSpec_image_basicOpen]
  exact equation_basicOpen_disjoint f U e
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open Scheme.Modules ActualSheafTensor
namespace AffineCartierNilpotence
variable {R : CommRingCat.{0}} (L : (Spec R).Modules)
    (e : L ≅ SheafOfModules.unit (Spec R).ringCatSheaf)
    (i : L ⟶ SheafOfModules.unit (Spec R).ringCatSheaf)

/-- The equation from the fully faithful affine functor is the trivialized ideal section under the structure-section isomorphism. -/
lemma equation_section :
    (Scheme.ΓSpecIso R).inv (equation L e i) =
      i.val.app (op ⊤) (e.inv.val.app (op ⊤) (1 : Γ(Spec R, ⊤))) := by
  let q : tilde (ModuleCat.of R R) ⟶ tilde (ModuleCat.of R R) := e.inv ≫ i
  let a := (tilde.functor R).preimage q
  have h := tilde.toOpen_map_app a ⊤
  have hq : tilde.map a = q := (tilde.functor R).map_preimage q
  rw [hq] at h
  have hh := congrArg (fun k : ModuleCat.of R R ⟶ _ => k 1) h
  change i.val.app (op ⊤) (e.inv.val.app (op ⊤)
      ((tilde.toOpen (ModuleCat.of R R) ⊤) 1)) =
    (tilde.toOpen (ModuleCat.of R R) ⊤) (equation L e i) at hh
  have hone : (tilde.toOpen (ModuleCat.of R R) ⊤) 1 = (1 : Γ(Spec R, ⊤)) := by
    exact map_one (Scheme.ΓSpecIso R).inv.hom
  rw [hone] at hh
  exact hh.symm
end AffineCartierNilpotence

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open scoped TensorProduct
namespace ActualSheafTensor
open Scheme.Modules
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- The coefficient-ring map for open-scheme restriction. -/
def openRingRestrictHom : X.ringCatSheaf ⟶
    (f.opensFunctor.sheafPushforwardContinuous RingCat
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj
      Y.ringCatSheaf :=
  ⟨Functor.whiskerRight
    ({ app V := (f.appIso V.unop).inv } :
      X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf)
    (forget₂ CommRingCat RingCat)⟩

/-- The concrete presheaf restriction underlying open-scheme restriction. -/
def openPresheafRestrict : PresheafOfModules.{0} Y.ringCatSheaf.obj ⥤
    PresheafOfModules.{0} X.ringCatSheaf.obj :=
  PresheafOfModules.pushforward (openRingRestrictHom f).hom

/-- Canonical open restriction comparison for module sheafification. -/
def openSheafifyRestrictMap (P : PresheafOfModules.{0} Y.ringCatSheaf.obj) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        ((openPresheafRestrict f).obj P) ⟶
      (restrictFunctor f).obj
        ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj P) :=
  ModuleSheafification.comparison f.opensFunctor (openRingRestrictHom f) P

instance openSheafifyRestrictMap_isIso (P : PresheafOfModules.{0} Y.ringCatSheaf.obj) :
    IsIso (openSheafifyRestrictMap f P) :=
  ModuleSheafification.comparison_isIso f.opensFunctor (openRingRestrictHom f) P

/-- Tensor presheaves commute with restriction to an open subscheme. -/
def openPresheafTensorRestrictIso (M N : PresheafOfModules.{0} Y.ringCatSheaf.obj) :
    (openPresheafRestrict f).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := Y.sheaf.obj) M N) ≅
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj)
      ((openPresheafRestrict f).obj M) ((openPresheafRestrict f).obj N) :=
  PresheafOfModules.isoMk (fun V =>
    (TensorChangeScalars.tensorEquiv (f.appIso V.unop).commRingCatIsoToRingEquiv
      (M.obj (op (f ''ᵁ V.unop))) (N.obj (op (f ''ᵁ V.unop)))).toModuleIso)
    (by
      intro V W g
      let P := (openPresheafRestrict f).obj
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := Y.sheaf.obj) M N)
      let Q := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.sheaf.obj)
        ((openPresheafRestrict f).obj M) ((openPresheafRestrict f).obj N)
      let eV := (TensorChangeScalars.tensorEquiv (f.appIso V.unop).commRingCatIsoToRingEquiv
        (M.obj (op (f ''ᵁ V.unop))) (N.obj (op (f ''ᵁ V.unop)))).toModuleIso
      let eW := (TensorChangeScalars.tensorEquiv (f.appIso W.unop).commRingCatIsoToRingEquiv
        (M.obj (op (f ''ᵁ W.unop))) (N.obj (op (f ''ᵁ W.unop)))).toModuleIso
      let B : ModuleCat (X.ringCatSheaf.obj.obj V) :=
        (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map g).hom).obj (Q.obj W)
      let a : P.obj V ⟶ B :=
        P.map g ≫ (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map g).hom).map eW.hom
      let b : P.obj V ⟶ B := eV.hom ≫ Q.map g
      apply ModuleCat.hom_ext
      change a.hom = b.hom
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul x y => rfl
      | add x y hx hy =>
        exact (a.hom.map_add x y).trans
          ((congrArg₂ (· + ·) hx hy).trans (b.hom.map_add x y).symm))


/-- The tensor sheaf commutes with open-scheme restriction. -/
def tensorOpenRestrictIso (M N : Y.Modules) :
    (restrictFunctor f).obj (tensor Y.sheaf M N) ≅
      tensor X.sheaf ((restrictFunctor f).obj M) ((restrictFunctor f).obj N) :=
  (@asIso _ _ _ _ (openSheafifyRestrictMap f
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := Y.sheaf.obj) M.val N.val))
    (openSheafifyRestrictMap_isIso f _)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (openPresheafTensorRestrictIso f M.val N.val)
/-- The inverse restriction comparison is the identity on pure sections,
with the scalar action transported by the open immersion's ring isomorphism. -/
lemma tensorOpenRestrictIso_inv_pure (M N : Y.Modules) (V : X.Opens)
    (x : ((restrictFunctor f).obj M).val.obj (op V))
    (y : ((restrictFunctor f).obj N).val.obj (op V)) :
    (tensorOpenRestrictIso f M N).inv.val.app (op V)
      (pure X.sheaf ((restrictFunctor f).obj M)
        ((restrictFunctor f).obj N) (op V) x y) =
    pure Y.sheaf M N (op (f ''ᵁ V)) x y := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := Y.sheaf.obj) M.val N.val
  let e := openPresheafTensorRestrictIso f M.val N.val
  let sh := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit
  have hn := η.naturality e.inv
  have hc := ModuleSheafification.comparison_unit f.opensFunctor
    (openRingRestrictHom f) P
  have hn' := congrArg (fun g => g.app (op V)
      (x ⊗ₜ[X.sheaf.obj.obj (op V)] y)) hn
  have hc' := congrArg (fun g => g.app (op V)
      (x ⊗ₜ[Y.sheaf.obj.obj (op (f ''ᵁ V))] y)) hc
  change (openSheafifyRestrictMap f P).val.app (op V)
    ((sh.map e.inv).val.app (op V)
      (pure X.sheaf ((restrictFunctor f).obj M)
        ((restrictFunctor f).obj N) (op V) x y)) = _
  change (η.app ((openPresheafRestrict f).obj P)).app (op V)
      (x ⊗ₜ[Y.sheaf.obj.obj (op (f ''ᵁ V))] y) =
    (sh.map e.inv).val.app (op V)
      (pure X.sheaf ((restrictFunctor f).obj M)
        ((restrictFunctor f).obj N) (op V) x y) at hn'
  change (openSheafifyRestrictMap f P).val.app (op V)
      ((η.app ((openPresheafRestrict f).obj P)).app (op V)
        (x ⊗ₜ[Y.sheaf.obj.obj (op (f ''ᵁ V))] y)) =
    pure Y.sheaf M N (op (f ''ᵁ V)) x y at hc'
  exact (congrArg ((openSheafifyRestrictMap f P).val.app (op V)) hn'.symm).trans hc'
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open scoped TensorProduct
namespace ActualSheafTensor
open Scheme.Modules

lemma tensorLeft_pure {C : Type} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat) [HasSheafify J AddCommGrpCat]
    [J.WEqualsLocallyBijective AddCommGrpCat]
    (L : SheafOfModules (ringSheaf R)) {M N : SheafOfModules (ringSheaf R)} (g : M ⟶ N)
    (U : Cᵒᵖ) (l : L.val.obj U) (m : M.val.obj U) :
    ((tensorLeft R L).map g).val.app U (pure R L M U l m) =
      pure R L N U l (g.val.app U m) := by
  let : MonoidalCategory (PresheafOfModules (ringSheaf R).obj) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModules (R.obj ⋙ forget₂ CommRingCat RingCat)))
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.naturality
    (L.val ◁ g.val)
  exact (congrArg (fun k => k.app U (l ⊗ₜ[R.obj.obj U] m)) h).symm

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]

private local instance restrictionSectionModule {Z : Scheme.{0}} (M : Z.Modules)
    (U : Z.Opensᵒᵖ) : Module (Z.sheaf.obj.obj U) (M.val.obj U) := (M.val.obj U).isModule

private lemma tensorOpenRestrict_naturality (L : Y.Modules) {M N : Y.Modules} (g : M ⟶ N) :
    let F : Y.Modules ⥤ X.Modules := restrictFunctor f
    let TY : Y.Modules ⥤ Y.Modules := tensorLeft Y.sheaf L
    let TX : X.Modules ⥤ X.Modules := tensorLeft X.sheaf (F.obj L)
    let eM : F.obj (TY.obj M) ≅ TX.obj (F.obj M) := tensorOpenRestrictIso f L M
    let eN : F.obj (TY.obj N) ≅ TX.obj (F.obj N) := tensorOpenRestrictIso f L N
    F.map (TY.map g) ≫ eN.hom = eM.hom ≫ TX.map (F.map g) := by
  dsimp only
  let F : Y.Modules ⥤ X.Modules := restrictFunctor f
  let TY : Y.Modules ⥤ Y.Modules := tensorLeft Y.sheaf L
  let TX : X.Modules ⥤ X.Modules := tensorLeft X.sheaf (F.obj L)
  let eM : F.obj (TY.obj M) ≅ TX.obj (F.obj M) := tensorOpenRestrictIso f L M
  let eN : F.obj (TY.obj N) ≅ TX.obj (F.obj N) := tensorOpenRestrictIso f L N
  change F.map (TY.map g) ≫ eN.hom = eM.hom ≫ TX.map (F.map g)
  have : Epi eM.inv := @IsIso.epi_of_iso _ _ _ _ _ eM.isIso_inv
  apply (cancel_epi eM.inv).mp
  erw [eM.inv_hom_id_assoc]
  apply tensor_hom_ext X.sheaf
  intro U l m
  let x₁ := pure X.sheaf (F.obj L) (F.obj M) U l m
  let x₂ := pure X.sheaf (F.obj L) (F.obj N) U l ((F.map g).val.app U m)
  let y₁ := pure Y.sheaf L M (op (f ''ᵁ U.unop)) l m
  let y₂ := pure Y.sheaf L N (op (f ''ᵁ U.unop)) l ((F.map g).val.app U m)
  have hm : eM.inv.val.app U x₁ = y₁ :=
    tensorOpenRestrictIso_inv_pure f L M U.unop l m
  have hy : (F.map (TY.map g)).val.app U y₁ = y₂ :=
    tensorLeft_pure Y.sheaf L g (op (f ''ᵁ U.unop)) l m
  have hn : eN.inv.val.app U x₂ = y₂ :=
    tensorOpenRestrictIso_inv_pure f L N U.unop l ((F.map g).val.app U m)
  have hx : (TX.map (F.map g)).val.app U x₁ = x₂ :=
    tensorLeft_pure X.sheaf (F.obj L) (F.map g) U l m
  have hi := congrArg (fun k => k.val.app U x₂) eN.inv_hom_id
  change eN.hom.val.app U (eN.inv.val.app U x₂) = x₂ at hi
  change eN.hom.val.app U ((F.map (TY.map g)).val.app U (eM.inv.val.app U x₁)) =
    (TX.map (F.map g)).val.app U x₁
  exact (congrArg (fun z => eN.hom.val.app U ((F.map (TY.map g)).val.app U z)) hm).trans
    ((congrArg (eN.hom.val.app U) hy).trans
      ((congrArg (eN.hom.val.app U) hn.symm).trans (hi.trans hx.symm)))

/-- Restriction of tensoring is natural, with the coefficient changes. -/
def tensorOpenRestrictNatIso (L : Y.Modules) :
    tensorLeft Y.sheaf L ⋙ restrictFunctor f ≅
      restrictFunctor f ⋙ tensorLeft X.sheaf ((restrictFunctor f).obj L) :=
  NatIso.ofComponents (fun M => tensorOpenRestrictIso f L M)
    (fun g => tensorOpenRestrict_naturality f L g)

/-- Restriction of the ideal inclusion. -/
def restrictedIdeal {L : Y.Modules} (i : L ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    (restrictFunctor f).obj L ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (restrictFunctor f).map i ≫ (restrictUnitIso f).hom

lemma tensorOpenRestrict_action {L : Y.Modules}
    (i : L ⟶ SheafOfModules.unit Y.ringCatSheaf) (M : Y.Modules) :
    (tensorOpenRestrictIso f L M).hom ≫
      (idealAction X.sheaf (restrictedIdeal f i)).app ((restrictFunctor f).obj M) =
    (restrictFunctor f).map ((idealAction Y.sheaf i).app M) := by
  have : Epi (tensorOpenRestrictIso f L M).inv :=
    @IsIso.epi_of_iso _ _ _ _ _ (tensorOpenRestrictIso f L M).isIso_inv
  apply (cancel_epi (tensorOpenRestrictIso f L M).inv).mp
  erw [Iso.inv_hom_id_assoc]
  apply tensor_hom_ext X.sheaf
  intro U l m
  change ((idealAction X.sheaf (restrictedIdeal f i)).app
      ((restrictFunctor f).obj M)).val.app U (pure X.sheaf _ _ U l m) =
    ((restrictFunctor f).map ((idealAction Y.sheaf i).app M)).val.app U
      ((tensorOpenRestrictIso f L M).inv.val.app U (pure X.sheaf _ _ U l m))
  have hleft := idealAction_pure X.sheaf (restrictedIdeal f i)
    ((restrictFunctor f).obj M) U l m
  change ((idealAction X.sheaf (restrictedIdeal f i)).app
    ((restrictFunctor f).obj M)).val.app U (pure X.sheaf _ _ U l m) = _ at hleft
  rw [hleft, tensorOpenRestrictIso_inv_pure]
  change _ = ((idealAction Y.sheaf i).app M).val.app (op (f ''ᵁ U.unop))
    (pure Y.sheaf L M _ l m)
  have hright := idealAction_pure Y.sheaf i M (op (f ''ᵁ U.unop)) l m
  change ((idealAction Y.sheaf i).app M).val.app (op (f ''ᵁ U.unop))
    (pure Y.sheaf L M _ l m) = _ at hright
  rw [hright]
  let : Module Γ(Y, f ''ᵁ U.unop) (M.val.obj (op (f ''ᵁ U.unop))) :=
    (M.val.obj (op (f ''ᵁ U.unop))).isModule
  let m' : M.val.obj (op (f ''ᵁ U.unop)) := m
  change ((f.appIso U.unop).inv ((f.appIso U.unop).hom (i.val.app _ l))) • m' = _
  have h := congrArg (fun k => k (i.val.app _ l)) (f.appIso U.unop).hom_inv_id
  change (f.appIso U.unop).inv ((f.appIso U.unop).hom (i.val.app _ l)) = _ at h
  rw [h]
  rfl

end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
open Scheme.Modules ActualSheafTensor
variable {X Y : Scheme.{0}} (g : X ⟶ Y)
    {R : CommRingCat.{0}} (f : Spec R ⟶ Y) [IsOpenImmersion f]
    (e : (restrictFunctor f).obj (idealSheaf g) ≅ SheafOfModules.unit (Spec R).ringCatSheaf)

/-- On an affine trivializing chart, the principal equation extracted
by full faithfulness has nonvanishing open disjoint from the divisor. -/
lemma chart_equation_disjoint :
    g ⁻¹ᵁ (f ''ᵁ PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation
      ((restrictFunctor f).obj (idealSheaf g)) e (restrictedIdeal f (idealι g)))) = ⊥ := by
  let L := (restrictFunctor f).obj (idealSheaf g)
  let i := restrictedIdeal f (idealι g)
  let t := AffineCartierNilpotence.equation L e i
  change g ⁻¹ᵁ (f ''ᵁ PrimeSpectrum.basicOpen t) = ⊥
  rw [← basicOpen_eq_of_affine t, Scheme.image_basicOpen, Scheme.preimage_basicOpen]
  have he := AffineCartierNilpotence.equation_section L e i
  rw [he]
  let l : (idealSheaf g).val.obj (op (f ''ᵁ (⊤ : (Spec R).Opens))) :=
    e.inv.val.app (op ⊤) (1 : Γ(Spec R, ⊤))
  have hring : (f.appIso ⊤).inv (i.val.app (op ⊤)
      (e.inv.val.app (op ⊤) (1 : Γ(Spec R, ⊤)))) = (idealι g).val.app _ l := by
    change (f.appIso ⊤).inv ((f.appIso ⊤).hom ((idealι g).val.app _ l)) = _
    exact congrArg (fun k => k ((idealι g).val.app _ l)) (f.appIso ⊤).hom_inv_id
  rw [hring]
  have hz := congrArg (fun k : idealSheaf g ⟶
      (pushforward g).obj (SheafOfModules.unit X.ringCatSheaf) =>
        k.val.app (op (f ''ᵁ (⊤ : (Spec R).Opens))) l) (kernel.condition (structureMap g))
  change g.app _ ((idealι g).val.app _ l) = 0 at hz
  rw [hz, Scheme.basicOpen_zero]
end ActualCartier

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualOpenSupport
open Scheme.Modules
variable {X Y : Scheme.{0}}

/-- Vanishing of a sheaf on an open persists on every smaller open. -/
lemma isZero_over_of_le (M : Y.Modules) {U V : Y.Opens} (hUV : U ≤ V)
    (hM : IsZero (M.over V)) : IsZero (M.over U) := by
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let E := SheafOfModules.evaluation.{0} (Y.ringCatSheaf.over V)
    (op (Over.mk (homOfLE ((leOfHom W.unop.hom).trans hUV))))
  have : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hz := E.map_isZero hM
  have : Subsingleton (M.val.obj (op W.unop.left)) := ModuleCat.subsingleton_of_isZero hz
  exact Subsingleton.elim (α := M.val.obj (op W.unop.left)) _ _

/-- Restriction along an open immersion preserves vanishing on the image open. -/
lemma isZero_restrict_over_of_image (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (V : X.Opens) (hM : IsZero (M.over (f ''ᵁ V))) :
    IsZero (((restrictFunctor f).obj M).over V) := by
  rw [IsZero.iff_id_eq_zero]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hW : f ''ᵁ W.unop.left ≤ f ''ᵁ V :=
    f.opensFunctor.monotone (leOfHom W.unop.hom)
  let E := SheafOfModules.evaluation.{0} (Y.ringCatSheaf.over (f ''ᵁ V))
    (op (Over.mk (homOfLE hW)))
  have : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hz := E.map_isZero hM
  have : Subsingleton (M.val.obj (op (f ''ᵁ W.unop.left))) :=
    ModuleCat.subsingleton_of_isZero hz
  exact Subsingleton.elim (α := M.val.obj (op (f ''ᵁ W.unop.left))) _ _

/-- Vanishing on the open subscheme is equivalent to vanishing on
the slice site; this direction is needed for an exact quotient's support. -/
lemma isZero_over_of_restrict (M : Y.Modules) (U : Y.Opens)
    (hM : IsZero ((restrictFunctor U.ι).obj M)) : IsZero (M.over U) := by
  let e : M.over U ≅ (overEquiv U).inverse.obj ((restrictFunctor U.ι).obj M) :=
    (overEquiv U).unitIso.app _ ≪≫
      (overEquiv U).inverse.mapIso ((overFunctorEquiv U).app M)
  exact ((overEquiv U).inverse.map_isZero hM).of_iso e

/-- The open complement of a closed immersion. -/
def complement (g : X ⟶ Y) [IsClosedImmersion g] : Y.Opens :=
  ⟨(Set.range g)ᶜ, g.isClosedEmbedding.isClosed_range.isOpen_compl⟩

lemma le_complement {g : X ⟶ Y} [IsClosedImmersion g] (U : Y.Opens)
    (hU : g ⁻¹ᵁ U = ⊥) : U ≤ complement g := by
  intro y hy
  change y ∉ Set.range g
  rintro ⟨x, rfl⟩
  have h : x ∈ g ⁻¹ᵁ U := hy
  rw [hU] at h
  exact h

/-- Geometric support on the divisor implies vanishing on every
restricted open whose image is disjoint from it. -/
lemma isZero_restrict_of_disjoint (g : X ⟶ Y) [IsClosedImmersion g]
    {Z : Scheme.{0}} (f : Z ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (hM : IsZero (M.over (complement g)))
    (V : Z.Opens) (hV : g ⁻¹ᵁ (f ''ᵁ V) = ⊥) :
    IsZero (((restrictFunctor f).obj M).over V) :=
  isZero_restrict_over_of_image f M V
    (isZero_over_of_le M (le_complement (f ''ᵁ V) hV) hM)
end ActualOpenSupport

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
open Scheme.Modules ActualSheafTensor CartierImageFiltration
variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y]
    (g : X ⟶ Y) [IsClosedImmersion g]
    {R : CommRingCat.{0}} (f : Spec R ⟶ Y) [IsOpenImmersion f]
    (eL : (restrictFunctor f).obj (idealSheaf g) ≅
      SheafOfModules.unit (Spec R).ringCatSheaf)

/-- The geometric puncture lies above the affine Cartier nonvanishing open,
so its fixed isomorphism restricts to the affine principal puncture. -/
def chartPunctureIso (M N : Y.Modules)
    (e : M.over (ActualOpenSupport.complement g) ≅
      N.over (ActualOpenSupport.complement g)) :
    let L := (restrictFunctor f).obj (idealSheaf g)
    let U := PrimeSpectrum.basicOpen
      (AffineCartierNilpotence.equation L eL (restrictedIdeal f (idealι g)))
    ((restrictFunctor f).obj M).over U ≅ ((restrictFunctor f).obj N).over U :=
  ActualOpenComparison.pullOverIso f _ _
    (ActualOpenSupport.le_complement _ (chart_equation_disjoint g f eL)) e

private local instance schemeSheafSectionModule (M : Y.Modules) (V : Y.Opensᵒᵖ) :
    Module (Y.sheaf.obj.obj V) (M.val.obj V) := (M.val.obj V).isModule

/-- Each affine trivializing chart admits a uniform bound in both directions
for ideal-twisted embeddings of torsion-free lattices identified off the divisor. -/
lemma exists_chart_uniform_sandwich (M N : Y.Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (M.val.obj V))
    (hN : ∀ V, Module.IsTorsionFree (Y.sheaf.obj.obj V) (N.val.obj V))
    (e : M.over (ActualOpenSupport.complement g) ≅
      N.over (ActualOpenSupport.complement g)) :
    let L := (restrictFunctor f).obj (idealSheaf g)
    let i := restrictedIdeal f (idealι g)
    let U := PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation L eL i)
    let T := tensorLeft (Spec R).sheaf L
    let act := idealAction (Spec R).sheaf i
    let Mf := (restrictFunctor f).obj M
    let Nf := (restrictFunctor f).obj N
    ∃ k : ℕ, ∀ n : ℕ, k ≤ n →
      ∃ (a : (power T n).obj Mf ⟶ Nf) (b : (power T n).obj Nf ⟶ Mf),
        Mono a ∧ Mono b ∧
        a.over U = ((powerAction T act n).app Mf).over U ≫
          (chartPunctureIso g f eL M N e).hom ∧
        b.over U = ((powerAction T act n).app Nf).over U ≫
          (chartPunctureIso g f eL M N e).inv := by
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion f
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.mp inferInstance
  have : ((restrictFunctor f).obj M).IsFinitePresentation :=
    CoherentGlobal.coherent_restrict f M
  have : ((restrictFunctor f).obj N).IsFinitePresentation :=
    CoherentGlobal.coherent_restrict f N
  have : Mono (idealι g) := by
    exact equalizer.ι_mono (C := SheafOfModules Y.ringCatSheaf)
  have : Mono (restrictedIdeal f (idealι g)) := by
    exact mono_comp' (Functor.map_mono (restrictFunctor f) (idealι g))
      (@IsIso.mono_of_iso _ _ _ _ _ (restrictUnitIso f).isIso_hom)
  exact CartierAffineLattice.exists_uniform_twisted_sandwich _ eL _ _ _
    (SheafTorsion.restrict f M hM) (SheafTorsion.restrict f N hN)
    (chartPunctureIso g f eL M N e)
end ActualCartier

end

noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualCartier
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    (U : Y.Opens) (hU : IsAffineOpen U) (e : SectionTrivialization f U)

include hU in
/-- The Cartier principal open equals the geometric puncture of the affine chart. -/
lemma equation_basicOpen_eq_puncture :
    Y.basicOpen (equation f U e) = U ⊓ ActualOpenSupport.complement f := by
  have hk : (f.ker.support : Set Y) = Set.range f := by
    rw [Scheme.Hom.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq]
  have hs (y : Y) (hy : y ∈ U) :
      y ∈ Set.range f ↔ y ∉ Y.basicOpen (equation f U e) := by
    rw [← hk]
    change y ∈ f.ker.support ↔ y ∉ Y.basicOpen (equation f U e)
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hy]
    rw [Scheme.Hom.ker_apply, kernel_eq_span_equation f U e,
      Scheme.zeroLocus_span, Scheme.zeroLocus_singleton]
    rfl
  ext y
  constructor
  · intro hy
    have hyU : y ∈ U := Y.basicOpen_le (equation f U e) hy
    exact ⟨hyU, fun hr => (hs y hyU).mp hr hy⟩
  · rintro ⟨hyU, hy⟩
    change y ∉ Set.range f at hy
    exact Classical.not_not.mp (fun hn => hy ((hs y hyU).mpr hn))
end ActualCartier

end

noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualCartier
open Scheme.Modules ActualSheafTensor
variable {X Y : Scheme.{0}} (g : X ⟶ Y)
    {R : CommRingCat.{0}} (f : Spec R ⟶ Y) [IsOpenImmersion f]
    (e : (restrictFunctor f).obj (idealSheaf g) ≅
      SheafOfModules.unit (Spec R).ringCatSheaf)

private local instance schemeOpenSectionModule (M : Y.Modules) (U : Y.Opens) :
    Module Γ(Y, U) (M.val.obj (op U)) := (M.val.obj (op U)).isModule

/-- An affine-scheme line trivialization gives the section
trivialization on its image open, accounting for the coefficient-ring iso. -/
def chartSectionTrivialization : SectionTrivialization g (f ''ᵁ (⊤ : (Spec R).Opens)) where
  toFun l := (f.appIso ⊤).inv (e.hom.val.app (op ⊤) l)
  invFun r := e.inv.val.app (op ⊤) ((f.appIso ⊤).hom r)
  left_inv l := by
    change e.inv.val.app (op ⊤) ((f.appIso ⊤).hom
      ((f.appIso ⊤).inv (e.hom.val.app (op ⊤) l))) = l
    erw [CommRingCat.hom_inv_apply]
    exact congrArg (fun k => k.val.app (op ⊤) l) e.hom_inv_id
  right_inv r := by
    change (f.appIso ⊤).inv (e.hom.val.app (op ⊤)
      (e.inv.val.app (op ⊤) ((f.appIso ⊤).hom r))) = r
    have h := congrArg (fun k => k.val.app (op ⊤) ((f.appIso ⊤).hom r)) e.inv_hom_id
    change e.hom.val.app (op ⊤) (e.inv.val.app (op ⊤) ((f.appIso ⊤).hom r)) =
      ((f.appIso ⊤).hom r : Γ(Spec R, ⊤)) at h
    rw [h, CommRingCat.inv_hom_apply]
  map_add' l m := by
    erw [map_add, map_add]
  map_smul' r l := by
    have h := (e.hom.val.app (op ⊤)).hom.map_smul ((f.appIso ⊤).hom r) l
    change e.hom.val.app (op ⊤) ((f.appIso ⊤).inv ((f.appIso ⊤).hom r) • l) =
      @HMul.hMul Γ(Spec R, ⊤) Γ(Spec R, ⊤) Γ(Spec R, ⊤) inferInstance
        ((f.appIso ⊤).hom r) (e.hom.val.app (op ⊤) l) at h
    rw [CommRingCat.inv_hom_apply] at h
    change (f.appIso ⊤).inv (e.hom.val.app (op ⊤) (r • l)) =
      r * (f.appIso ⊤).inv (e.hom.val.app (op ⊤) l)
    erw [h, map_mul, CommRingCat.inv_hom_apply]

/-- The abstract affine equation used for denominator clearing is the
actual-ideal generator under the scheme's section-ring iso. -/
lemma chart_equation_section :
    (f.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv
      (AffineCartierNilpotence.equation ((restrictFunctor f).obj (idealSheaf g))
        e (restrictedIdeal f (idealι g)))) =
      equation g (f ''ᵁ (⊤ : (Spec R).Opens)) (chartSectionTrivialization g f e) := by
  rw [AffineCartierNilpotence.equation_section]
  change (f.appIso ⊤).inv ((f.appIso ⊤).hom ((idealι g).val.app _
      (e.inv.val.app (op ⊤) (1 : Γ(Spec R, ⊤))))) =
      (idealι g).val.app _ (e.inv.val.app (op ⊤) ((f.appIso ⊤).hom 1))
  erw [CommRingCat.inv_hom_apply, map_one (f.appIso ⊤).hom.hom]
  rfl
/-- Exact agreement of the affine principal open and the geometric Cartier
puncture, including its image in the ambient scheme. -/
lemma chart_equation_image_eq_puncture [IsClosedImmersion g] :
    f ''ᵁ PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation
      ((restrictFunctor f).obj (idealSheaf g)) e (restrictedIdeal f (idealι g))) =
        f.opensRange ⊓ ActualOpenSupport.complement g := by
  rw [← basicOpen_eq_of_affine, Scheme.image_basicOpen, chart_equation_section]
  rw [equation_basicOpen_eq_puncture g _
    ((isAffineOpen_top (Spec R)).image_of_isOpenImmersion f),
    Scheme.Hom.image_top_eq_opensRange]

/-- The local principal puncture on the chart is precisely the inverse
image of the open complement of the closed divisor. -/
lemma chart_equation_puncture_eq_preimage [IsClosedImmersion g] :
    PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation
      ((restrictFunctor f).obj (idealSheaf g)) e (restrictedIdeal f (idealι g))) =
        f ⁻¹ᵁ ActualOpenSupport.complement g := by
  let V : (Spec R).Opens := PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation
      ((restrictFunctor f).obj (idealSheaf g)) e (restrictedIdeal f (idealι g)))
  calc V = f ⁻¹ᵁ (f ''ᵁ V) := (f.preimage_image_eq V).symm
       _ = f ⁻¹ᵁ (f ''ᵁ (f ⁻¹ᵁ ActualOpenSupport.complement g)) := by
         rw [chart_equation_image_eq_puncture,
           Scheme.Hom.image_preimage_eq_opensRange_inf]
       _ = f ⁻¹ᵁ ActualOpenSupport.complement g := f.preimage_image_eq _

end ActualCartier


end

end OAI
