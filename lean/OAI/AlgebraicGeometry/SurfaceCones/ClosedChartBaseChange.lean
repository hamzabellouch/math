import OAI.AlgebraicGeometry.SurfaceCones.ChartDominance

namespace OAI

/-! Closed base change on the completed source charts. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace SourcePullbackChart
open KummerSourceModel SourceConeMorphism SourceZeroSections
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra
  originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

def completedClosedChartBaseChangeIso (i : Fin 3)
    (M : (Spec (.of (completedSourceChart i))).Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback (completedPlaneZeroChart i)).obj
      ((Scheme.Modules.pushforward (completedProjection i)).obj M) ≅
      (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))).obj
        ((Scheme.Modules.pullback (completedZeroChart i)).obj M) :=
  AffineClosedBaseChange.sheafIso _ _ _ _ (completedClosedChart_isPushout i) M
end SourcePullbackChart

end

/-! Identification of affine tensor-product base change with the canonical mate. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry TensorProduct
namespace AffineClosedBaseChange
variable {B C D E : CommRingCat.{0}}
  (f : B ⟶ C) (z : B ⟶ D) (w : C ⟶ E) (q : D ⟶ E)
  (h : IsPushout f z w q)

def moduleRightIso :
    ModuleCat.restrictScalars w.hom ⋙ ModuleCat.restrictScalars f.hom ≅
      ModuleCat.restrictScalars q.hom ⋙ ModuleCat.restrictScalars z.hom :=
  (ModuleCat.restrictScalarsComp f.hom w.hom).symm ≪≫
    ModuleCat.restrictScalarsCongr (congrArg CommRingCat.Hom.hom h.w) ≪≫
    ModuleCat.restrictScalarsComp z.hom q.hom

lemma moduleRightIso_apply (M : ModuleCat E) (m : M) :
    (moduleRightIso f z w q h).hom.app M m = m := rfl

def moduleMate :
    ModuleCat.restrictScalars f.hom ⋙ ModuleCat.extendScalars z.hom ⟶
      ModuleCat.extendScalars w.hom ⋙ ModuleCat.restrictScalars q.hom :=
  (((mateEquiv (ModuleCat.extendRestrictScalarsAdj w.hom)
    (ModuleCat.extendRestrictScalarsAdj z.hom)).symm
      (TwoSquare.mk _ _ _ _ (moduleRightIso f z w q h).hom)).natTrans)

lemma moduleMate_one_tmul (M : ModuleCat C) (m : M) :
    (moduleMate f z w q h).app M
      ((ModuleCat.extendRestrictScalarsAdj z.hom).unit.app _
        (m : (ModuleCat.restrictScalars f.hom).obj M)) =
      (ModuleCat.extendRestrictScalarsAdj w.hom).unit.app M m := by
  have H := unit_mateEquiv_symm (ModuleCat.extendRestrictScalarsAdj w.hom)
    (ModuleCat.extendRestrictScalarsAdj z.hom)
    (TwoSquare.mk _ _ _ _ (moduleRightIso f z w q h).hom) M
  change (ModuleCat.restrictScalars f.hom).map
      ((ModuleCat.extendRestrictScalarsAdj w.hom).unit.app M) ≫
        (moduleRightIso f z w q h).hom.app _ =
    (ModuleCat.extendRestrictScalarsAdj z.hom).unit.app _ ≫
      (ModuleCat.restrictScalars z.hom).map ((moduleMate f z w q h).app M) at H
  have H' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom H) m
  change (moduleRightIso f z w q h).hom.app ((ModuleCat.extendScalars w.hom).obj M)
      ((ModuleCat.extendRestrictScalarsAdj w.hom).unit.app M m) =
    (moduleMate f z w q h).app M ((ModuleCat.extendRestrictScalarsAdj z.hom).unit.app _ m) at H'
  erw [moduleRightIso_apply] at H'
  exact H'.symm

lemma moduleMate_eq (M : ModuleCat C) :
    (moduleMate f z w q h).app M = (moduleIso f z w q h M).hom := by
  let : Algebra B C := f.hom.toAlgebra
  let : Algebra B D := z.hom.toAlgebra
  let : Algebra C E := w.hom.toAlgebra
  let : Algebra D E := q.hom.toAlgebra
  let : Algebra B E := (w.hom.comp f.hom).toAlgebra
  let : IsScalarTower B C E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower B D E :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  let : Algebra.IsPushout B D C E := CommRingCat.isPushout_iff_isPushout.mp h.flip
  let : Module B M := Module.compHom M f.hom
  let : IsScalarTower B C M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let F : D ⊗[B] M →ₗ[D] E ⊗[C] M := ((moduleMate f z w q h).app M).hom
  let G : D ⊗[B] M →ₗ[D] E ⊗[C] M :=
    (Algebra.IsPushout.cancelBaseChange B D C E M).symm.toLinearMap
  suffices he : F = G from ModuleCat.hom_ext he
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul d m =>
    rw [show d ⊗ₜ[B] m = d • ((1 : D) ⊗ₜ[B] m) by rw [smul_tmul', smul_eq_mul, mul_one]]
    rw [F.map_smul, G.map_smul]
    congr 1
    have he : F ((1 : D) ⊗ₜ[B] m) = (1 : E) ⊗ₜ[C] m :=
      moduleMate_one_tmul f z w q h M m
    rw [he]
    symm
    simpa only [G, LinearEquiv.coe_coe, map_one] using
      (Algebra.IsPushout.cancelBaseChange_symm_tmul B D C E M (1 : D) m)

instance moduleMate_app_isIso (M : ModuleCat C) : IsIso ((moduleMate f z w q h).app M) := by
  rw [moduleMate_eq]
  infer_instance

instance moduleMate_isIso : IsIso (moduleMate f z w q h) := by
  apply NatIso.isIso_of_isIso_app
end AffineClosedBaseChange

end

/-! The canonical base-change transformation attached to a commutative square of schemes. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualSheafBaseChange
open Scheme.Modules
variable {B C D E : Scheme.{0}}
  (f : C ⟶ B) (z : D ⟶ B) (w : E ⟶ C) (q : E ⟶ D)
  (h : w ≫ f = q ≫ z)

def rightIso : pushforward w ⋙ pushforward f ≅ pushforward q ⋙ pushforward z :=
  pushforwardComp w f ≪≫ pushforwardCongr h ≪≫ (pushforwardComp q z).symm

def mate : pushforward f ⋙ pullback z ⟶ pullback w ⋙ pushforward q :=
  (((mateEquiv (pullbackPushforwardAdjunction w) (pullbackPushforwardAdjunction z)).symm
    (TwoSquare.mk _ _ _ _ (rightIso f z w q h).hom)).natTrans)

lemma mate_unit (M : C.Modules) :
    (pushforward f).map ((pullbackPushforwardAdjunction w).unit.app M) ≫
      (rightIso f z w q h).hom.app _ =
    (pullbackPushforwardAdjunction z).unit.app _ ≫
      (pushforward z).map ((mate f z w q h).app M) :=
  unit_mateEquiv_symm (pullbackPushforwardAdjunction w) (pullbackPushforwardAdjunction z)
    (TwoSquare.mk _ _ _ _ (rightIso f z w q h).hom) M

lemma mate_eq_iff (M : C.Modules)
    (φ : (Scheme.Modules.pullback z).obj ((pushforward f).obj M) ⟶
      (pushforward q).obj ((Scheme.Modules.pullback w).obj M)) :
    (mate f z w q h).app M = φ ↔
    (pullbackPushforwardAdjunction z).unit.app _ ≫ (pushforward z).map φ =
      (pushforward f).map ((pullbackPushforwardAdjunction w).unit.app M) ≫
        (rightIso f z w q h).hom.app _ := by
  rw [mate_unit]
  exact ⟨fun he => by rw [he], fun he =>
    ((pullbackPushforwardAdjunction z).homEquiv _ _).injective he.symm⟩
end ActualSheafBaseChange

end

/-! The commuting restriction-of-scalars square is the square on affine global sections, including
the canonical scheme pushforward comparison. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace AffineClosedBaseChange
lemma rotate_iso_square {K : Type*} [Category K] {A B C D : K}
    (l : A ≅ B) (r : C ≅ D) {a : B ⟶ D} {b : A ⟶ C}
    (h : l.hom ≫ a = b ≫ r.hom) : l.inv ≫ b = a ≫ r.inv := by
  rw [l.inv_comp_eq, ← Category.assoc, r.eq_comp_inv]
  exact h.symm
variable {B C D E : CommRingCat.{0}}
  (f : B ⟶ C) (z : B ⟶ D) (w : C ⟶ E) (q : D ⟶ E)
  (h : IsPushout f z w q)
include h in
lemma spec_square : Spec.map w ≫ Spec.map f = Spec.map q ≫ Spec.map z := by
  rw [← Spec.map_comp, ← Spec.map_comp, h.w]

lemma gamma_cube (M : (Spec E).Modules) :
    (AffinePullback.pushforwardGammaIso f).hom.app
        ((Scheme.Modules.pushforward (Spec.map w)).obj M) ≫
      (ModuleCat.restrictScalars f.hom).map ((AffinePullback.pushforwardGammaIso w).hom.app M) ≫
      (moduleRightIso f z w q h).hom.app (moduleSpecΓFunctor.obj M) =
    moduleSpecΓFunctor.map
      ((ActualSheafBaseChange.rightIso (Spec.map f) (Spec.map z)
        (Spec.map w) (Spec.map q) (spec_square f z w q h)).hom.app M) ≫
      (AffinePullback.pushforwardGammaIso z).hom.app
        ((Scheme.Modules.pushforward (Spec.map q)).obj M) ≫
      (ModuleCat.restrictScalars z.hom).map ((AffinePullback.pushforwardGammaIso q).hom.app M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  simp only [ActualSheafBaseChange.rightIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp]
  change m = (((Scheme.Modules.pushforwardCongr
    (spec_square f z w q h)).hom.app M).app ⊤) m
  rw [Scheme.Modules.pushforwardCongr_hom_app_app]
  change m = M.presheaf.map (𝟙 (Opposite.op ⊤)) m
  rw [M.presheaf.map_id]
  rfl
lemma gamma_cube_inv (M : (Spec E).Modules) :
    (ModuleCat.restrictScalars f.hom).map ((AffinePullback.pushforwardGammaIso w).inv.app M) ≫
      (AffinePullback.pushforwardGammaIso f).inv.app
        ((Scheme.Modules.pushforward (Spec.map w)).obj M) ≫
      moduleSpecΓFunctor.map
        ((ActualSheafBaseChange.rightIso (Spec.map f) (Spec.map z)
          (Spec.map w) (Spec.map q) (spec_square f z w q h)).hom.app M) =
    (moduleRightIso f z w q h).hom.app (moduleSpecΓFunctor.obj M) ≫
      (ModuleCat.restrictScalars z.hom).map ((AffinePullback.pushforwardGammaIso q).inv.app M) ≫
      (AffinePullback.pushforwardGammaIso z).inv.app
        ((Scheme.Modules.pushforward (Spec.map q)).obj M) := by
  let eL := (AffinePullback.pushforwardGammaIso f).app
      ((Scheme.Modules.pushforward (Spec.map w)).obj M) ≪≫
    (ModuleCat.restrictScalars f.hom).mapIso ((AffinePullback.pushforwardGammaIso w).app M)
  let eR := (AffinePullback.pushforwardGammaIso z).app
      ((Scheme.Modules.pushforward (Spec.map q)).obj M) ≪≫
    (ModuleCat.restrictScalars z.hom).mapIso ((AffinePullback.pushforwardGammaIso q).app M)
  have H : eL.hom ≫ (moduleRightIso f z w q h).hom.app (moduleSpecΓFunctor.obj M) =
      moduleSpecΓFunctor.map
        ((ActualSheafBaseChange.rightIso (Spec.map f) (Spec.map z)
          (Spec.map w) (Spec.map q) (spec_square f z w q h)).hom.app M) ≫ eR.hom := by
    dsimp only [eL, eR, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    rw [Category.assoc]
    exact gamma_cube f z w q h M
  have Hi := rotate_iso_square eL eR H
  simpa only [eL, eR, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using Hi
end AffineClosedBaseChange

end

/-! Unit compatibility for the affine associated-sheaf isomorphism, identifying tensor-product base
change with canonical base change. -/
noncomputable section
open CategoryTheory
namespace AdjunctionBCUnit
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
  {T : C ⥤ D} {U : D ⥤ C} {T' : C' ⥤ D'} {U' : D' ⥤ C'}
  {L : D ⥤ D'} {R : D' ⥤ D} {L' : C ⥤ C'} {R' : C' ⥤ C}
  (a : T ⊣ U) (b : T' ⊣ U') (c : L ⊣ R) (d : L' ⊣ R')
  (α : R ⋙ U ≅ U' ⋙ R')

def leftIso : T ⋙ L ≅ L' ⋙ T' :=
  ((conjugateIsoEquiv (a.comp c) (d.comp b)).symm α).symm

def pushComparison (N : C') : T.obj (R'.obj N) ⟶ R.obj (T'.obj N) :=
  (a.homEquiv _ _).symm (R'.map (b.unit.app N) ≫ α.inv.app (T'.obj N))

lemma unit_pushComparison (N : C') :
    a.unit.app _ ≫ U.map (pushComparison a b α N) =
      R'.map (b.unit.app N) ≫ α.inv.app (T'.obj N) :=
  (a.homEquiv _ _).apply_symm_apply _

lemma pushComparison_naturality {N N' : C'} (k : N ⟶ N') :
    T.map (R'.map k) ≫ pushComparison a b α N' =
      pushComparison a b α N ≫ R.map (T'.map k) := by
  apply (a.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [a.unit_naturality_assoc]
  rw [unit_pushComparison]
  rw [reassoc_of% (unit_pushComparison a b α N)]
  have hn := α.inv.naturality (T'.map k)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun k' => R'.map k' ≫ α.inv.app (T'.obj N')) (b.unit_naturality k).symm

lemma unit_comparison (M : C) :
    c.unit.app (T.obj M) ≫ R.map ((leftIso a b c d α).hom.app M) =
      T.map (d.unit.app M) ≫ pushComparison a b α (L'.obj M) := by
  apply (a.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  apply (cancel_mono (α.hom.app (T'.obj (L'.obj M)))).mp
  have h := unit_conjugateEquiv_symm (a.comp c) (d.comp b) α.hom M
  simp only [Adjunction.comp_unit_app, Category.assoc, Functor.comp_obj, Functor.comp_map] at h
  change a.unit.app M ≫ U.map (c.unit.app (T.obj M)) ≫ α.hom.app (L.obj (T.obj M)) =
    d.unit.app M ≫ R'.map (b.unit.app (L'.obj M)) ≫
      R'.map (U'.map ((leftIso a b c d α).inv.app M)) at h
  have ht := congrArg (fun k => k ≫ R'.map (U'.map ((leftIso a b c d α).hom.app M))) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at ht
  have hn := α.hom.naturality ((leftIso a b c d α).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn] at ht
  simp only [Category.assoc]
  rw [ht]
  have hn2 := a.unit.naturality (d.unit.app M)
  simp only [Functor.id_map, Functor.id_obj, Functor.comp_map, Functor.comp_obj] at hn2
  rw [← Category.assoc, ← hn2, Category.assoc, reassoc_of% (unit_pushComparison a b α (L'.obj M))]
  simp only [α.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  rw [U'.map_id (T'.obj (L'.obj M)), Category.comp_id]
end AdjunctionBCUnit

end

/-! Compatibility of the affine associated-sheaf isomorphisms with pullback-pushforward units. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace AffinePullback
variable {A B : CommRingCat.{0}} (f : A ⟶ B)

lemma pushComparison_eq (M : ModuleCat B) :
    AdjunctionBCUnit.pushComparison (tilde.adjunction (R := A))
      (tilde.adjunction (R := B)) (pushforwardGammaIso f) M =
        (pushforwardTildeIso f M).inv := by
  unfold AdjunctionBCUnit.pushComparison pushforwardTildeIso
  dsimp only [Iso.trans, Iso.symm, Functor.mapIso, Iso.app]
  rw [Adjunction.homEquiv_counit]
  rfl

lemma pullbackTildeIso_unit (M : ModuleCat A) :
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).unit.app (tilde M) ≫
      (Scheme.Modules.pushforward (Spec.map f)).map ((pullbackTildeIso f).hom.app M) =
    (tilde.functor A).map ((ModuleCat.extendRestrictScalarsAdj f.hom).unit.app M) ≫
      (pushforwardTildeIso f ((ModuleCat.extendScalars f.hom).obj M)).inv := by
  have H := AdjunctionBCUnit.unit_comparison (tilde.adjunction (R := A))
    (tilde.adjunction (R := B))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))
    (ModuleCat.extendRestrictScalarsAdj f.hom) (pushforwardGammaIso f) M
  rw [pushComparison_eq] at H
  exact H
lemma pushforwardTildeIso_inv_unit (M : ModuleCat B) :
    (tilde.adjunction (R := A)).unit.app _ ≫
        moduleSpecΓFunctor.map (pushforwardTildeIso f M).inv =
      (ModuleCat.restrictScalars f.hom).map ((tilde.adjunction (R := B)).unit.app M) ≫
        (pushforwardGammaIso f).inv.app (tilde M) := by
  have H := AdjunctionBCUnit.unit_pushComparison (tilde.adjunction (R := A))
      (tilde.adjunction (R := B)) (pushforwardGammaIso f) M
  rw [pushComparison_eq] at H
  exact H

lemma pushforwardTildeIso_inv_naturality {M N : ModuleCat B} (k : M ⟶ N) :
    (tilde.functor A).map ((ModuleCat.restrictScalars f.hom).map k) ≫
        (pushforwardTildeIso f N).inv =
      (pushforwardTildeIso f M).inv ≫
        (Scheme.Modules.pushforward (Spec.map f)).map ((tilde.functor B).map k) := by
  have H := AdjunctionBCUnit.pushComparison_naturality (tilde.adjunction (R := A))
    (tilde.adjunction (R := B)) (pushforwardGammaIso f) k
  rw [pushComparison_eq] at H
  exact H
lemma gamma_pushTilde_comp {C : CommRingCat.{0}} (g : B ⟶ C) (M : ModuleCat C) :
    (tilde.adjunction (R := A)).unit.app _ ≫
      moduleSpecΓFunctor.map
        ((pushforwardTildeIso f ((ModuleCat.restrictScalars g.hom).obj M)).inv ≫
          (Scheme.Modules.pushforward (Spec.map f)).map (pushforwardTildeIso g M).inv) =
    (ModuleCat.restrictScalars f.hom).map
        ((ModuleCat.restrictScalars g.hom).map ((tilde.adjunction (R := C)).unit.app M)) ≫
      (ModuleCat.restrictScalars f.hom).map ((pushforwardGammaIso g).inv.app (tilde M)) ≫
      (pushforwardGammaIso f).inv.app
        ((Scheme.Modules.pushforward (Spec.map g)).obj (tilde M)) := by
  erw [(moduleSpecΓFunctor (R := A)).map_comp, ← Category.assoc,
    pushforwardTildeIso_inv_unit f ((ModuleCat.restrictScalars g.hom).obj M), Category.assoc]
  have hn := (pushforwardGammaIso f).inv.naturality (pushforwardTildeIso g M).inv
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [← hn, ← Category.assoc, ← (ModuleCat.restrictScalars f.hom).map_comp,
    pushforwardTildeIso_inv_unit g M, (ModuleCat.restrictScalars f.hom).map_comp, Category.assoc]
end AffinePullback

end

/-! Coherence for the two affine pushforward comparisons. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace AffineClosedBaseChange
variable {B C D E : CommRingCat.{0}}
  (f : B ⟶ C) (z : B ⟶ D) (w : C ⟶ E) (q : D ⟶ E)
  (h : IsPushout f z w q)
lemma push_cube (M : ModuleCat E) :
    (AffinePullback.pushforwardTildeIso f ((ModuleCat.restrictScalars w.hom).obj M)).inv ≫
      (Scheme.Modules.pushforward (Spec.map f)).map (AffinePullback.pushforwardTildeIso w M).inv ≫
      (ActualSheafBaseChange.rightIso (Spec.map f) (Spec.map z)
        (Spec.map w) (Spec.map q) (spec_square f z w q h)).hom.app (tilde M) =
    (tilde.functor B).map ((moduleRightIso f z w q h).hom.app M) ≫
      (AffinePullback.pushforwardTildeIso z ((ModuleCat.restrictScalars q.hom).obj M)).inv ≫
      (Scheme.Modules.pushforward (Spec.map z)).map (AffinePullback.pushforwardTildeIso q M).inv := by
  apply (tilde.adjunction (R := B)).homEquiv _ _ |>.injective
  erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [← Category.assoc, (moduleSpecΓFunctor (R := B)).map_comp, ← Category.assoc,
    AffinePullback.gamma_pushTilde_comp f w M]
  conv_rhs =>
    erw [(moduleSpecΓFunctor (R := B)).map_comp,
      (tilde.adjunction (R := B)).unit_naturality_assoc
        ((moduleRightIso f z w q h).hom.app M)]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  conv_rhs => erw [AffinePullback.gamma_pushTilde_comp z q M]
  simp only [Category.assoc]
  erw [gamma_cube_inv f z w q h]
  have hn := (moduleRightIso f z w q h).hom.naturality
    ((tilde.adjunction (R := E)).unit.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  change (ModuleCat.restrictScalars f.hom).map
        ((ModuleCat.restrictScalars w.hom).map ((tilde.adjunction (R := E)).unit.app M)) ≫
      (moduleRightIso f z w q h).hom.app (moduleSpecΓFunctor.obj (tilde M)) =
    (moduleRightIso f z w q h).hom.app M ≫
      (ModuleCat.restrictScalars z.hom).map
        ((ModuleCat.restrictScalars q.hom).map ((tilde.adjunction (R := E)).unit.app M)) at hn
  erw [← Category.assoc, ← Category.assoc, hn, Category.assoc, Category.assoc]
end AffineClosedBaseChange

end

/-! The affine closed base-change isomorphism is the canonical mate. This is the compatibility
needed for its use on the main model's open cover. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace AffineClosedBaseChange
variable {B C D E : CommRingCat.{0}}
  (f : B ⟶ C) (z : B ⟶ D) (w : C ⟶ E) (q : D ⟶ E)
  (h : IsPushout f z w q)
local notation "Pf" => Scheme.Modules.pushforward (Spec.map f)
local notation "Pz" => Scheme.Modules.pushforward (Spec.map z)
local notation "Pw" => Scheme.Modules.pushforward (Spec.map w)
local notation "Pq" => Scheme.Modules.pushforward (Spec.map q)
local notation "Lz" => Scheme.Modules.pullback (Spec.map z)
local notation "Lw" => Scheme.Modules.pullback (Spec.map w)
local notation "Rf" => ModuleCat.restrictScalars f.hom
local notation "Rz" => ModuleCat.restrictScalars z.hom
local notation "Rw" => ModuleCat.restrictScalars w.hom
local notation "Rq" => ModuleCat.restrictScalars q.hom
local notation "Ez" => ModuleCat.extendScalars z.hom
local notation "Ew" => ModuleCat.extendScalars w.hom
local notation "TB" => tilde.functor B
local notation "TC" => tilde.functor C
local notation "TD" => tilde.functor D
local notation "TE" => tilde.functor E
local notation "δ" => ActualSheafBaseChange.rightIso (Spec.map f) (Spec.map z)
  (Spec.map w) (Spec.map q) (spec_square f z w q h)
local notation "α" => moduleRightIso f z w q h

lemma moduleMate_unit (M : ModuleCat C) :
    (ModuleCat.extendRestrictScalarsAdj z.hom).unit.app ((Rf).obj M) ≫
        (Rz).map (moduleIso f z w q h M).hom =
      (Rf).map ((ModuleCat.extendRestrictScalarsAdj w.hom).unit.app M) ≫ (α).hom.app ((Ew).obj M) := by
  have H := unit_mateEquiv_symm (ModuleCat.extendRestrictScalarsAdj w.hom)
    (ModuleCat.extendRestrictScalarsAdj z.hom)
    (TwoSquare.mk _ _ _ _ (α).hom) M
  change _ = _ ≫ (Rz).map ((moduleMate f z w q h).app M) at H
  rw [moduleMate_eq] at H
  exact H.symm

lemma tildeMate_eq (M : ModuleCat C) :
    (ActualSheafBaseChange.mate (Spec.map f) (Spec.map z) (Spec.map w) (Spec.map q)
      (spec_square f z w q h)).app (tilde M) = (tildeIso f z w q h M).hom := by
  apply (ActualSheafBaseChange.mate_eq_iff _ _ _ _ _ _ _).2
  apply (cancel_mono ((Pz).map ((Pq).map ((AffinePullback.pullbackTildeIso w).hom.app M)))).mp
  let fa : (Lz).obj ((Pf).obj (tilde M)) ⟶ (Lz).obj (tilde ((Rf).obj M)) :=
    (Lz).map (AffinePullback.pushforwardTildeIso f M).hom
  let fb : (Lz).obj (tilde ((Rf).obj M)) ⟶ tilde ((Ez).obj ((Rf).obj M)) :=
    (AffinePullback.pullbackTildeIso z).hom.app ((Rf).obj M)
  let fc : tilde ((Ez).obj ((Rf).obj M)) ⟶ tilde ((Rq).obj ((Ew).obj M)) :=
    (TD).map (moduleIso f z w q h M).hom
  let fd : tilde ((Rq).obj ((Ew).obj M)) ⟶ (Pq).obj (tilde ((Ew).obj M)) :=
    (AffinePullback.pushforwardTildeIso q ((Ew).obj M)).inv
  let fe : (Pq).obj (tilde ((Ew).obj M)) ⟶ (Pq).obj ((Lw).obj (tilde M)) :=
    (Pq).map ((AffinePullback.pullbackTildeIso w).inv.app M)
  let u := (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map z)).unit.app ((Pf).obj (tilde M))
  let v := (Pf).map ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map w)).unit.app (tilde M))
  let dd := (δ).hom.app ((Lw).obj (tilde M))
  let k : (Pz).obj ((Pq).obj ((Lw).obj (tilde M))) ⟶
      (Pz).obj ((Pq).obj (tilde ((Ew).obj M))) :=
    (Pz).map ((Pq).map ((AffinePullback.pullbackTildeIso w).hom.app M))
  change (u ≫ (Pz).map (fa ≫ fb ≫ fc ≫ fd ≫ fe)) ≫ k = (v ≫ dd) ≫ k
  have hm : (Pz).map (fa ≫ fb ≫ fc ≫ fd ≫ fe) =
      (Pz).map fa ≫ (Pz).map fb ≫ (Pz).map fc ≫ (Pz).map fd ≫ (Pz).map fe := by
    simp only [Functor.map_comp]
  rw [hm]
  simp only [Category.assoc]
  have hc : (Pz).map fe ≫ k = 𝟙 _ := by
    dsimp only [fe, k]
    erw [← (Pz).map_comp, ← (Pq).map_comp, Iso.inv_hom_id_app, (Pq).map_id, (Pz).map_id]
  rw [hc, Category.comp_id]
  dsimp only [u, v, dd, k, fa, fb, fc, fd]
  erw [(Scheme.Modules.pullbackPushforwardAdjunction (Spec.map z)).unit_naturality_assoc]
  erw [reassoc_of% (AffinePullback.pullbackTildeIso_unit z ((Rf).obj M))]
  conv_lhs =>
    arg 2
    erw [Category.assoc]
    arg 2
    erw [← Category.assoc]
    arg 1
    erw [← AffinePullback.pushforwardTildeIso_inv_naturality z
      (moduleIso f z w q h M).hom]
  conv_lhs =>
    arg 2
    arg 2
    erw [Category.assoc]
  erw [← reassoc_of% ((TB).map_comp
    ((ModuleCat.extendRestrictScalarsAdj z.hom).unit.app ((Rf).obj M))
    ((Rz).map (moduleIso f z w q h M).hom))]
  erw [moduleMate_unit f z w q h M, Functor.map_comp]
  simp only [Category.assoc]
  erw [← push_cube f z w q h ((Ew).obj M)]
  conv_lhs =>
    arg 2
    erw [← Category.assoc]
  erw [reassoc_of% (AffinePullback.pushforwardTildeIso_inv_naturality f
    ((ModuleCat.extendRestrictScalarsAdj w.hom).unit.app M))]
  conv_lhs =>
    arg 2
    erw [Category.assoc]
  erw [Iso.hom_inv_id_assoc]
  erw [← reassoc_of% ((Pf).map_comp
    ((TC).map ((ModuleCat.extendRestrictScalarsAdj w.hom).unit.app M))
    (AffinePullback.pushforwardTildeIso w ((Ew).obj M)).inv)]
  erw [← AffinePullback.pullbackTildeIso_unit w M, Functor.map_comp]
  simp only [Category.assoc]
  have hn := (δ).hom.naturality ((AffinePullback.pullbackTildeIso w).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [hn]
  rfl

instance tildeMate_isIso (M : ModuleCat C) :
    IsIso ((ActualSheafBaseChange.mate (Spec.map f) (Spec.map z) (Spec.map w) (Spec.map q)
      (spec_square f z w q h)).app (tilde M)) := by
  rw [tildeMate_eq f z w q h M]
  infer_instance

instance sheafMate_isIso (M : (Spec C).Modules) [M.IsQuasicoherent] :
    IsIso ((ActualSheafBaseChange.mate (Spec.map f) (Spec.map z) (Spec.map w) (Spec.map q)
      (spec_square f z w q h)).app M) := by
  have : IsIso (Scheme.Modules.fromTildeΓ M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  apply (NatTrans.isIso_app_iff_of_iso _ (asIso (Scheme.Modules.fromTildeΓ M))).1
  exact tildeMate_isIso f z w q h (moduleSpecΓFunctor.obj M)
end AffineClosedBaseChange

end

/-! Transport of base-change mates along adjunction isomorphisms. -/
noncomputable section
open CategoryTheory
namespace ActualMateTransport
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {G : A ⥤ C} {H : B ⥤ D}
  {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
  {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₁' : L₁' ⊣ R₁') (a₂' : L₂' ⊣ R₂')
  (e₁ : R₁ ≅ R₁') (e₂ : R₂ ≅ R₂')

def left₁ : L₁' ≅ L₁ := (conjugateIsoEquiv a₁ a₁').symm e₁
def left₂ : L₂' ≅ L₂ := (conjugateIsoEquiv a₂ a₂').symm e₂

def square (s : TwoSquare R₁ H G R₂) : TwoSquare R₁' H G R₂' :=
  (s.whiskerTop e₁.inv).whiskerBottom e₂.hom

lemma square_refl (s : TwoSquare R₁ H G R₂) :
    square (Iso.refl R₁) (Iso.refl R₂) s = s := by
  ext M
  simp [square, TwoSquare.whiskerTop, TwoSquare.whiskerBottom]

lemma mate_transport (s : TwoSquare R₁ H G R₂) :
    (mateEquiv a₁' a₂').symm (square e₁ e₂ s) =
      (((mateEquiv a₁ a₂).symm s).whiskerLeft (left₁ a₁ a₁' e₁).inv).whiskerRight
        (left₂ a₂ a₂' e₂).hom := by
  apply (mateEquiv a₁' a₂').injective
  rw [Equiv.apply_symm_apply, mateEquiv_conjugateEquiv_vcomp,
    conjugateEquiv_mateEquiv_vcomp, Equiv.apply_symm_apply]
  simp only [left₁, left₂, conjugateIsoEquiv, Equiv.symm_mk, Equiv.coe_fn_mk,
    Equiv.apply_symm_apply, square]

lemma mate_transport_app (s : TwoSquare R₁ H G R₂) (M : A) :
    ((mateEquiv a₁' a₂').symm (square e₁ e₂ s)).natTrans.app M =
      (left₂ a₂ a₂' e₂).hom.app (G.obj M) ≫
        ((mateEquiv a₁ a₂).symm s).natTrans.app M ≫
          H.map ((left₁ a₁ a₁' e₁).inv.app M) := by
  rw [mate_transport]
  rfl

lemma mate_transport_isIso (s : TwoSquare R₁ H G R₂) (M : A)
    [IsIso (((mateEquiv a₁ a₂).symm s).natTrans.app M)] :
    IsIso (((mateEquiv a₁' a₂').symm (square e₁ e₂ s)).natTrans.app M) := by
  rw [mate_transport_app a₁ a₂ a₁' a₂' e₁ e₂ s M]
  infer_instance
end ActualMateTransport
namespace ActualMateTransport
universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {G : A ⥤ C} {H : B ⥤ D}
  {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
  {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₁' : L₁' ⊣ R₁') (a₂' : L₂' ⊣ R₂')
  (e₁ : R₁ ≅ R₁') (e₂ : R₂ ≅ R₂')
lemma mate_transport_isIso_iff (s : TwoSquare R₁ H G R₂) (M : A) :
    IsIso (((mateEquiv a₁' a₂').symm (square e₁ e₂ s)).natTrans.app M) ↔
      IsIso (((mateEquiv a₁ a₂).symm s).natTrans.app M) := by
  rw [mate_transport_app a₁ a₂ a₁' a₂' e₁ e₂ s M,
    isIso_comp_left_iff, isIso_comp_right_iff]
end ActualMateTransport

end

/-! The canonical base-change mate for an open restriction is invertible. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
namespace ActualSheafBaseChange
open Scheme.Modules
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma restrictMate_eq :
    (mateEquiv (restrictAdjunction (f ⁻¹ᵁ U).ι) (restrictAdjunction U.ι)).symm
      (TwoSquare.mk _ _ _ _ (rightIso f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U)
        (morphismRestrict_ι f U).symm).hom) = CoherentBaseChange.restrictSquare f U := by
  apply (mateEquiv (restrictAdjunction (f ⁻¹ᵁ U).ι) (restrictAdjunction U.ι)).injective
  rw [Equiv.apply_symm_apply]
  change _ = CoherentBaseChange.rightSquare f U
  exact (CoherentBaseChange.rightSquare_eq f U).symm

instance openMate_isIso (M : X.Modules) :
    IsIso ((mate f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U) (morphismRestrict_ι f U).symm).app M) := by
  let s := TwoSquare.mk _ _ _ _ (rightIso f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U)
    (morphismRestrict_ι f U).symm).hom
  have : IsIso (((mateEquiv (restrictAdjunction (f ⁻¹ᵁ U).ι)
      (restrictAdjunction U.ι)).symm s).natTrans.app M) := by
    dsimp only [s]
    rw [restrictMate_eq]
    exact inferInstanceAs (IsIso ((CoherentBaseChange.pushforwardRestrictNatIso f U).hom.app M))
  have H := ActualMateTransport.mate_transport_isIso
    (restrictAdjunction (f ⁻¹ᵁ U).ι) (restrictAdjunction U.ι)
    (pullbackPushforwardAdjunction (f ⁻¹ᵁ U).ι) (pullbackPushforwardAdjunction U.ι)
    (Iso.refl _) (Iso.refl _) s M
  rw [ActualMateTransport.square_refl] at H
  exact H
end ActualSheafBaseChange

end

/-! Horizontal composition of right-adjoint squares and their mates. This is a necessary locality
device for the closed base change. -/
noncomputable section
open CategoryTheory
open TwoSquare
namespace ActualMatePasting
universe u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅} {F : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Category.{v₄} D] [Category.{v₅} E] [Category.{v₆} F]
  {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
  (s : TwoSquare R₁ H G R₂) (t : TwoSquare R₃ K H R₄)

lemma mate_app (M : A) :
    ((mateEquiv a₁ a₂).symm s).natTrans.app M =
      L₂.map (G.map (a₁.unit.app M)) ≫ L₂.map (s.natTrans.app (L₁.obj M)) ≫
        a₂.counit.app (H.obj (L₁.obj M)) := by
  simp only [mateEquiv, Equiv.coe_fn_symm_mk, NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app, Functor.comp_map, Functor.comp_obj, Category.id_comp]
  erw [L₂.map_id, L₂.map_id]
  simp only [Category.id_comp]
  erw [Category.comp_id]

lemma mate_hcomp :
    (mateEquiv (a₁.comp a₃) (a₂.comp a₄)).symm (t ≫ₕ s) =
      ((mateEquiv a₁ a₂).symm s) ≫ᵥ ((mateEquiv a₃ a₄).symm t) := by
  apply (mateEquiv (a₁.comp a₃) (a₂.comp a₄)).injective
  rw [Equiv.apply_symm_apply, mateEquiv_hcomp, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]

lemma mate_hcomp_app (M : A) :
    ((mateEquiv (a₁.comp a₃) (a₂.comp a₄)).symm (t ≫ₕ s)).natTrans.app M =
      L₄.map (((mateEquiv a₁ a₂).symm s).natTrans.app M) ≫
        ((mateEquiv a₃ a₄).symm t).natTrans.app (L₁.obj M) := by
  rw [mate_hcomp]
  simp only [TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

lemma mate_hcomp_isIso (M : A)
    [IsIso (L₄.map (((mateEquiv a₁ a₂).symm s).natTrans.app M))]
    [IsIso (((mateEquiv a₃ a₄).symm t).natTrans.app (L₁.obj M))] :
    IsIso (((mateEquiv (a₁.comp a₃) (a₂.comp a₄)).symm (t ≫ₕ s)).natTrans.app M) := by
  rw [mate_hcomp_app]; infer_instance

lemma map_mate_isIso (M : A)
    [IsIso (((mateEquiv (a₁.comp a₃) (a₂.comp a₄)).symm (t ≫ₕ s)).natTrans.app M)]
    [IsIso (((mateEquiv a₃ a₄).symm t).natTrans.app (L₁.obj M))] :
    IsIso (L₄.map (((mateEquiv a₁ a₂).symm s).natTrans.app M)) := by
  have he := mate_hcomp_app a₁ a₂ a₃ a₄ s t M
  have : IsIso (L₄.map (((mateEquiv a₁ a₂).symm s).natTrans.app M) ≫
      ((mateEquiv a₃ a₄).symm t).natTrans.app (L₁.obj M)) := he ▸ inferInstance
  exact IsIso.of_isIso_comp_right _
    (((mateEquiv a₃ a₄).symm t).natTrans.app (L₁.obj M))
end ActualMatePasting

end

/-! Open Cartesian squares, including the source's affine charts, have invertible canonical base-
change mates. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualSheafBaseChange
open Scheme.Modules
variable {B C D E : Scheme.{0}}
  (f : C ⟶ B) (z : D ⟶ B) (w : E ⟶ C) (q : E ⟶ D)
  [IsOpenImmersion z] [IsOpenImmersion w]
  (h : IsPullback w q f z)

lemma restrict_map_app {M N : B.Modules} (φ : M ⟶ N) (U : D.Opens) :
    ((restrictFunctor z).map φ).app U = φ.app (z ''ᵁ U) := rfl

def restrictMate : pushforward f ⋙ restrictFunctor z ⟶ restrictFunctor w ⋙ pushforward q :=
  ((mateEquiv (restrictAdjunction w) (restrictAdjunction z)).symm
    (TwoSquare.mk _ _ _ _ (rightIso f z w q h.w).hom)).natTrans

lemma restrictMate_app_app (M : C.Modules) (U : D.Opens) :
    ((restrictMate f z w q h).app M).app U =
      M.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback h.flip U)).op := by
  unfold restrictMate
  rw [ActualMatePasting.mate_app]
  simp only [Scheme.Modules.Hom.comp_app, restrictAdjunction_counit_app_app]
  dsimp only [TwoSquare.mk, TwoSquare.natTrans]
  simp only [restrict_map_app, pushforward_map_app, restrictAdjunction_unit_app_app, rightIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Scheme.Modules.Hom.comp_app, pushforwardComp_hom_app_app, pushforwardComp_inv_app_app, pushforwardCongr_hom_app_app, restrict_map, pushforward_obj_presheaf_map]
  erw [Category.id_comp, ← M.presheaf.map_comp, ← M.presheaf.map_comp]
  congr 1

lemma restrictMate_isIso (M : C.Modules) : IsIso ((restrictMate f z w q h).app M) := by
  have HI : IsIso ((Scheme.Modules.toPresheaf D).map
      ((restrictMate f z w q h).app M)) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro U
    change IsIso (((restrictMate f z w q h).app M).app U.unop)
    rw [restrictMate_app_app]
    apply Functor.map_isIso
  exact isIso_of_reflects_iso _ (Scheme.Modules.toPresheaf D)

lemma openCartesianMate_isIso (M : C.Modules) : IsIso ((mate f z w q h.w).app M) := by
  let s := TwoSquare.mk _ _ _ _ (rightIso f z w q h.w).hom
  have : IsIso (((mateEquiv (restrictAdjunction w) (restrictAdjunction z)).symm s).natTrans.app M) :=
    restrictMate_isIso f z w q h M
  have H := ActualMateTransport.mate_transport_isIso
    (restrictAdjunction w) (restrictAdjunction z)
    (pullbackPushforwardAdjunction w) (pullbackPushforwardAdjunction z)
    (Iso.refl _) (Iso.refl _) s M
  rw [ActualMateTransport.square_refl] at H
  exact H
end ActualSheafBaseChange

end

/-! Pasting the canonical scheme-module base-change mates with actual pullback along composite
scheme morphisms. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
open TwoSquare
namespace ActualSheafBaseChange
open Scheme.Modules
variable {B C D E F G : Scheme.{0}}
  (f : C ⟶ B) (z : D ⟶ B) (w : E ⟶ C) (q : E ⟶ D)
  (h : w ≫ f = q ≫ z)
  (z' : F ⟶ D) (w' : G ⟶ E) (q' : G ⟶ F)
  (h' : w' ≫ q = q' ≫ z')

include h h' in
lemma paste_comm : (w' ≫ w) ≫ f = q' ≫ (z' ≫ z) := by
  rw [Category.assoc, h, ← Category.assoc w', h', Category.assoc]

def square := TwoSquare.mk _ _ _ _ (rightIso f z w q h).hom

lemma right_square_paste :
    ActualMateTransport.square (pushforwardComp w' w) (pushforwardComp z' z)
      ((square q z' w' q' h') ≫ₕ (square f z w q h)) =
      square f (z' ≫ z) (w' ≫ w) q' (paste_comm f z w q h z' w' q' h') := by
  apply TwoSquare.ext
  intro M
  apply Scheme.Modules.hom_ext
  intro U
  simp only [ActualMateTransport.square, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.hComp, square, rightIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Scheme.Modules.Hom.comp_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app, pushforward_map_app]
  change 𝟙 _ ≫ ((𝟙 _ ≫ M.presheaf.map _ ≫ 𝟙 _) ≫
    (𝟙 _ ≫ M.presheaf.map _ ≫ 𝟙 _)) ≫ 𝟙 _ =
    𝟙 _ ≫ M.presheaf.map _ ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  erw [← M.presheaf.map_comp]
  congr 1

lemma pasted_mate_isIso (M : C.Modules)
    [IsIso ((Scheme.Modules.pullback z').map ((mate f z w q h).app M))]
    [IsIso ((mate q z' w' q' h').app ((Scheme.Modules.pullback w).obj M))] :
    IsIso ((mate f (z' ≫ z) (w' ≫ w) q'
      (paste_comm f z w q h z' w' q' h')).app M) := by
  have : IsIso (((mateEquiv
      ((pullbackPushforwardAdjunction w).comp (pullbackPushforwardAdjunction w'))
      ((pullbackPushforwardAdjunction z).comp (pullbackPushforwardAdjunction z'))).symm
        ((square q z' w' q' h') ≫ₕ (square f z w q h))).natTrans.app M) :=
    by
      have H₁ : IsIso ((Scheme.Modules.pullback z').map
          (((mateEquiv (pullbackPushforwardAdjunction w) (pullbackPushforwardAdjunction z)).symm
            (square f z w q h)).natTrans.app M)) := ‹IsIso ((Scheme.Modules.pullback z').map ((mate f z w q h).app M))›
      have H₂ : IsIso (((mateEquiv (pullbackPushforwardAdjunction w') (pullbackPushforwardAdjunction z')).symm
          (square q z' w' q' h')).natTrans.app ((Scheme.Modules.pullback w).obj M)) :=
        ‹IsIso ((mate q z' w' q' h').app ((Scheme.Modules.pullback w).obj M))›
      exact ActualMatePasting.mate_hcomp_isIso _ _ _ _ _ _ M
  have H := ActualMateTransport.mate_transport_isIso
    ((pullbackPushforwardAdjunction w).comp (pullbackPushforwardAdjunction w'))
    ((pullbackPushforwardAdjunction z).comp (pullbackPushforwardAdjunction z'))
    (pullbackPushforwardAdjunction (w' ≫ w)) (pullbackPushforwardAdjunction (z' ≫ z))
    (pushforwardComp w' w) (pushforwardComp z' z)
    ((square q z' w' q' h') ≫ₕ (square f z w q h)) M
  rw [right_square_paste] at H
  exact H
lemma mate_isIso_congr (M : C.Modules) {z₂ : D ⟶ B} {w₂ : E ⟶ C}
    (hz : z = z₂) (hw : w = w₂) (h₂ : w₂ ≫ f = q ≫ z₂) :
    IsIso ((mate f z w q h).app M) ↔ IsIso ((mate f z₂ w₂ q h₂).app M) := by
  subst z₂; subst w₂; rfl

lemma map_mate_of_pasted_isIso (M : C.Modules)
    [IsIso ((mate f (z' ≫ z) (w' ≫ w) q'
      (paste_comm f z w q h z' w' q' h')).app M)]
    [IsIso ((mate q z' w' q' h').app ((Scheme.Modules.pullback w).obj M))] :
    IsIso ((Scheme.Modules.pullback z').map ((mate f z w q h).app M)) := by
  have he := ActualMateTransport.mate_transport_isIso_iff
    ((pullbackPushforwardAdjunction w).comp (pullbackPushforwardAdjunction w'))
    ((pullbackPushforwardAdjunction z).comp (pullbackPushforwardAdjunction z'))
    (pullbackPushforwardAdjunction (w' ≫ w)) (pullbackPushforwardAdjunction (z' ≫ z))
    (pushforwardComp w' w) (pushforwardComp z' z)
    ((square q z' w' q' h') ≫ₕ (square f z w q h)) M
  rw [right_square_paste] at he
  have HI : IsIso (((mateEquiv
      ((pullbackPushforwardAdjunction w).comp (pullbackPushforwardAdjunction w'))
      ((pullbackPushforwardAdjunction z).comp (pullbackPushforwardAdjunction z'))).symm
        ((square q z' w' q' h') ≫ₕ (square f z w q h))).natTrans.app M) := he.mp
          ‹IsIso ((mate f (z' ≫ z) (w' ≫ w) q'
            (paste_comm f z w q h z' w' q' h')).app M)›
  have H₂ : IsIso (((mateEquiv (pullbackPushforwardAdjunction w') (pullbackPushforwardAdjunction z')).symm
      (square q z' w' q' h')).natTrans.app ((Scheme.Modules.pullback w).obj M)) :=
        ‹IsIso ((mate q z' w' q' h').app ((Scheme.Modules.pullback w).obj M))›
  exact ActualMatePasting.map_mate_isIso
    (pullbackPushforwardAdjunction w) (pullbackPushforwardAdjunction z)
    (pullbackPushforwardAdjunction w') (pullbackPushforwardAdjunction z')
    (square f z w q h) (square q z' w' q' h') M
end ActualSheafBaseChange

end

end OAI
