import OAI.AlgebraicGeometry.SurfaceCones.GlobalBaseChange

namespace OAI

/-!
# Closed base change, affine denominator clearing and coherent Grothendieck groups

This development accompanies *A Complete Local Domain without a Small
Cohen–Macaulay Module* (OpenAI, 2026).
-/

/-! Pullback of the plane zero-section structure sheaf in the closed Cartesian square,
used to compare the Cartier ideals and conormal lines. -/
noncomputable section
open _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace SourcePullbackChart
open KummerSourceModel SourceConeMorphism SourceZeroSections Scheme.Modules ActualSheafBaseChange
attribute [local instance] integralSurfaceCommRing integralSurfaceSemiring
  integralPullbackCommRing integralPullbackSemiring pullbackBaseAlgebra surfaceOriginAlgebra
  completedPullbackModule completedPullbackAction completedPullbackSMul completedPullbackTower
  completedSurfaceModule completedSeriesModule completedSourceChartCommRing completedSourceChartSemiring
  completedSourceAlgebra
  originChartCommRing originChartSemiring originPlaneCommRing originPlaneSemiring
  chartBaseAlgebra planeOriginAlgebra baseChartModule baseChartAction baseChartSMul baseChartTower
  planeOriginModule completedBlowupCommRing completedBlowupSemiring completedBlowupAlgebra

lemma completedClosedChart_swappedMate_isIso (i : Fin 3)
    (M : (Spec (.of (planeChart i))).Modules) [M.IsQuasicoherent] :
    IsIso ((mate (completedPlaneZeroChart i) (completedProjection i)
      (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i))) (completedZeroChart i)
      (completedClosedChart_commute i).symm).app M) := by
  exact AffineClosedBaseChange.sheafMate_isIso _ _ _ _
    (completedClosedChart_isPushout i).flip M

lemma swappedActualMate_chart_isIso (M : ExplicitCone.plane.Modules) [M.IsQuasicoherent]
    (i : Fin 3) :
    IsIso ((Scheme.Modules.pullback (completedIota i)).map
      ((mate completedPlaneZero g ExplicitCone.projectiveNormalization completedSourceZero
        completedSourceZero_g.symm).app M)) := by
  have Ho : IsIso ((mate completedPlaneZero (completedBlowupIota i)
      (planeIota i) (completedPlaneZeroChart i) (planeIota_completedPlaneZero i)).app M) :=
    openCartesianMate_isIso _ _ _ _ (completedPlaneZeroChart_isPullback i) M
  have : ((Scheme.Modules.pullback (planeIota i)).obj M).IsQuasicoherent := open_pullback_qc _ M
  have Hc := completedClosedChart_swappedMate_isIso i ((Scheme.Modules.pullback (planeIota i)).obj M)
  have Hp := pasted_mate_isIso completedPlaneZero (completedBlowupIota i) (planeIota i)
    (completedPlaneZeroChart i) (planeIota_completedPlaneZero i)
    (completedProjection i) (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))
    (completedZeroChart i) (completedClosedChart_commute i).symm M
  have Hp' : IsIso ((mate completedPlaneZero ((completedIota i) ≫ g)
      ((surfaceIota i) ≫ ExplicitCone.projectiveNormalization) (completedZeroChart i)
      (paste_comm completedPlaneZero g ExplicitCone.projectiveNormalization completedSourceZero
        completedSourceZero_g.symm (completedIota i) (surfaceIota i)
        (completedZeroChart i) (surfaceIota_completedSourceZero i))).app M) := by
    exact (mate_isIso_congr _ _ _ _ _ M
      (completedIota_projection i).symm (surface_chart_square i).symm _).mp Hp
  have Hs := openCartesianMate_isIso completedSourceZero (completedIota i)
    (surfaceIota i) (completedZeroChart i) (completedZero_isPullback i)
    ((Scheme.Modules.pullback ExplicitCone.projectiveNormalization).obj M)
  exact map_mate_of_pasted_isIso completedPlaneZero g ExplicitCone.projectiveNormalization
    completedSourceZero completedSourceZero_g.symm (completedIota i) (surfaceIota i)
    (completedZeroChart i) (surfaceIota_completedSourceZero i) M

lemma swappedActualMate_isIso (M : ExplicitCone.plane.Modules) [M.IsQuasicoherent] :
    IsIso ((mate completedPlaneZero g ExplicitCone.projectiveNormalization completedSourceZero
      completedSourceZero_g.symm).app M) := by
  let φ := (mate completedPlaneZero g ExplicitCone.projectiveNormalization completedSourceZero
    completedSourceZero_g.symm).app M
  apply CoherentGlobal.isIso_of_open_cover (fun i : Fin 3 => (completedIota i).opensRange)
    completedCover.iSup_opensRange φ
  intro i
  have hi := swappedActualMate_chart_isIso M i
  have hr : IsIso ((restrictFunctor (completedIota i)).map φ) :=
    ((NatIso.isIso_map_iff (restrictFunctorIsoPullback (completedIota i)) φ)).mpr hi
  let e := (restrictFunctorComp (completedIota i).isoOpensRange.inv (completedIota i)).symm ≪≫
    restrictFunctorCongr (Scheme.Hom.isoOpensRange_inv_comp (completedIota i))
  have hx : IsIso (((restrictFunctor (completedIota i)) ⋙
      restrictFunctor (completedIota i).isoOpensRange.inv).map φ) := by
    change IsIso ((restrictFunctor (completedIota i).isoOpensRange.inv).map
      ((restrictFunctor (completedIota i)).map φ))
    infer_instance
  exact ((NatIso.isIso_map_iff e φ)).mp hx
end SourcePullbackChart

end

/-! A full-depth module is free over the compatible power-series parameter ring. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace SourceConeMorphism
open KummerSourceModel
abbrev completedParameterSpec := Spec.map
  (CommRingCat.ofHom ExplicitCone.projectiveCompletedParameterHom.toRingHom)
abbrev parameterModule (M : ModuleCat.{0} ExplicitCone.completedRing) : ModuleCat.{0} A :=
  (ModuleCat.restrictScalars ExplicitCone.projectiveCompletedParameterHom.toRingHom).obj M

lemma parameters_preimage_puncture : completedParameterSpec ⁻¹ᵁ seriesPuncture =
    ExplicitCone.completedPunctureOpen := by
  rw [seriesPuncture]
  erw [Scheme.Hom.preimage_iSup]
  rw [← ExplicitCone.completedProjectiveOpen_eq]
  congr 1
  funext i
  change PrimeSpectrum.basicOpen (ExplicitCone.projectiveCompletedParameterHom (MvPowerSeries.X i)) = _
  rw [← ExplicitCone.completedProjectiveSection_eq]

lemma parameterModule_free (M : ModuleCat.{0} ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] [Nontrivial M]
    (hdepth : SmallCM.localDepth ExplicitCone.completedRing M = 3) :
    Module.Free A (parameterModule M) :=
  ExplicitCone.projective_parameters_free_of_CM M hdepth

instance parameterModule_finite (M : ModuleCat.{0} ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] : Module.Finite A (parameterModule M) := by
  let : Algebra A ExplicitCone.completedRing :=
    ExplicitCone.projectiveCompletedParameterHom.toRingHom.toAlgebra
  let : Module.Finite A ExplicitCone.completedRing :=
    ExplicitCone.projectiveCompletedParameterHom_finite
  let := Module.restrictScalars A ExplicitCone.completedRing M
  let : IsScalarTower A ExplicitCone.completedRing M :=
    IsScalarTower.restrictScalars A ExplicitCone.completedRing M
  change Module.Finite A M
  exact Module.Finite.trans ExplicitCone.completedRing M

def basisIndex (M : ModuleCat.{0} ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] [Nontrivial M]
    (hdepth : SmallCM.localDepth ExplicitCone.completedRing M = 3) : Type :=
  let := parameterModule_free M hdepth
  Module.Free.ChooseBasisIndex A (parameterModule M)

instance basisIndex_finite (M : ModuleCat.{0} ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] [Nontrivial M]
    (hdepth : SmallCM.localDepth ExplicitCone.completedRing M = 3) : Finite (basisIndex M hdepth) := by
  let := parameterModule_free M hdepth
  change Finite (Module.Free.ChooseBasisIndex A (parameterModule M))
  infer_instance

def parameterSheafFreeIso (M : ModuleCat.{0} ExplicitCone.completedRing)
    [Module.Finite ExplicitCone.completedRing M] [Nontrivial M]
    (hdepth : SmallCM.localDepth ExplicitCone.completedRing M = 3) :
    (pushforward completedParameterSpec).obj (tilde M) ≅
      SheafOfModules.free (basisIndex M hdepth) := by
  let := parameterModule_free M hdepth
  let b := Module.Free.chooseBasis A (parameterModule M)
  let e : parameterModule M ≅ ModuleCat.of A (basisIndex M hdepth →₀ A) := b.repr.toModuleIso
  exact AffinePullback.pushforwardTildeIso (CommRingCat.ofHom ExplicitCone.projectiveCompletedParameterHom.toRingHom) M ≪≫
    (tilde.functor (CommRingCat.of A)).mapIso e ≪≫ tildeFinsupp (R := CommRingCat.of A) _
end SourceConeMorphism

end

/-! Sheaf comparisons along a puncture isomorphism. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace IsoPuncturePushforward
variable {X Y : Scheme.{0}}

local instance map_final (f : X ⟶ Y) : (TopologicalSpace.Opens.map f.base).Final :=
  Functor.final_of_exists_of_isFiltered _
    (fun U => ⟨⊤, ⟨homOfLE (by change U ≤ ⊤; exact le_top)⟩⟩)
    (fun {U V} s t => ⟨V, 𝟙 _, Subsingleton.elim _ _⟩)

def pushPullIso (f : X ⟶ Y) [IsIso f] (M : Y.Modules) :
    (pushforward f).obj ((pullback f).obj M) ≅ M :=
  (pushforward f).mapIso ((restrictFunctorIsoPullback f).symm.app M) ≪≫
    (CoherentGlobal.pushforwardIsoRestrict (asIso f)).app _ ≪≫
    (restrictFunctorComp (inv f) f).symm.app M ≪≫
    (restrictFunctorCongr (IsIso.inv_hom_id f)).app M ≪≫
    restrictFunctorId.app M

def restrictFreeIso (j : X ⟶ Y) [IsOpenImmersion j] (I : Type) :
    (restrictFunctor j).obj (SheafOfModules.free I) ≅ SheafOfModules.free I := by
  let : (SheafOfModules.pushforward j.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction j).isRightAdjoint
  exact (restrictFunctorIsoPullback j).app _ ≪≫
    SheafOfModules.pullbackObjFreeIso j.toRingCatSheafHom I

def pushFreeIso (f : X ⟶ Y) [IsIso f] (I : Type) :
    (pushforward f).obj (SheafOfModules.free I) ≅ SheafOfModules.free I := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  exact (pushforward f).mapIso (SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I).symm ≪≫
    pushPullIso f _

def pushforwardComparison (f : X ⟶ Y) (U : Y.Opens) [IsIso (f ∣_ U)]
    (E : X.Modules) (M : Y.Modules)
    (e : (pullback (f ⁻¹ᵁ U).ι).obj E ≅
      (pullback (f ∣_ U)).obj ((pullback U.ι).obj M)) :
    (restrictFunctor U.ι).obj ((pushforward f).obj E) ≅ (restrictFunctor U.ι).obj M :=
  CoherentBaseChange.pushforwardRestrictIso f U E ≪≫
    (pushforward (f ∣_ U)).mapIso
      ((restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app E ≪≫ e) ≪≫
    pushPullIso (f ∣_ U) _ ≪≫ (restrictFunctorIsoPullback U.ι).symm.app M

def reflectFreeIso (f : X ⟶ Y) [IsIso f] (M : X.Modules) (I : Type)
    (e : (pushforward f).obj M ≅ SheafOfModules.free I) :
    M ≅ SheafOfModules.free I :=
  (Functor.FullyFaithful.ofFullyFaithful (pushforward f)).preimageIso
    (e ≪≫ (pushFreeIso f I).symm)
end IsoPuncturePushforward

end

/-! Trivialization of the finite pushforward away from the exceptional divisor,
obtained from freeness over the parameter ring. -/
noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Scheme.Modules
namespace SourceConeMorphism
open KummerSourceModel SourcePullbackChart

/-- Pushforward along the commuting parameter square. -/
def pushforwardOverBaseIso (M : ModuleCat.{0} ExplicitCone.completedRing) :
    (pushforward completedBlowdown).obj (modelPushforward M) ≅
      (pushforward completedParameterSpec).obj ((pushforward p).obj (E M)) :=
  (pushforwardComp g completedBlowdown).app (E M) ≪≫
    (pushforwardCongr p_parameters.symm).app (E M) ≪≫
    (pushforwardComp p completedParameterSpec).symm.app (E M)

variable (M : ModuleCat.{0} ExplicitCone.completedRing)
  [Module.Finite ExplicitCone.completedRing M] [Nontrivial M]
  (hdepth : SmallCM.localDepth ExplicitCone.completedRing M = 3)

def p_puncturePushforwardIso :
    (restrictFunctor ExplicitCone.completedPunctureOpen.ι).obj ((pushforward p).obj (E M)) ≅
      (restrictFunctor ExplicitCone.completedPunctureOpen.ι).obj (tilde M) :=
  IsoPuncturePushforward.pushforwardComparison p ExplicitCone.completedPunctureOpen
    (E M) (tilde M) (E_punctureIso M hdepth)

def p_parametersPunctureIso :
    (restrictFunctor (completedParameterSpec ⁻¹ᵁ seriesPuncture).ι).obj
      ((pushforward p).obj (E M)) ≅
    (restrictFunctor (completedParameterSpec ⁻¹ᵁ seriesPuncture).ι).obj (tilde M) := by
  rw [parameters_preimage_puncture]
  exact p_puncturePushforwardIso M hdepth

def overBasePunctureComparison :
    (restrictFunctor seriesPuncture.ι).obj
      ((pushforward completedBlowdown).obj (modelPushforward M)) ≅
    (restrictFunctor seriesPuncture.ι).obj
      ((pushforward completedParameterSpec).obj (tilde M)) :=
  (restrictFunctor seriesPuncture.ι).mapIso (pushforwardOverBaseIso M) ≪≫
    CoherentBaseChange.pushforwardRestrictIso completedParameterSpec seriesPuncture
      ((pushforward p).obj (E M)) ≪≫
    (pushforward (completedParameterSpec ∣_ seriesPuncture)).mapIso
      (p_parametersPunctureIso M hdepth) ≪≫
    (CoherentBaseChange.pushforwardRestrictIso completedParameterSpec seriesPuncture (tilde M)).symm

def overBasePunctureFreeIso :
    (restrictFunctor seriesPuncture.ι).obj
      ((pushforward completedBlowdown).obj (modelPushforward M)) ≅
    SheafOfModules.free (basisIndex M hdepth) :=
  overBasePunctureComparison M hdepth ≪≫
    (restrictFunctor seriesPuncture.ι).mapIso (parameterSheafFreeIso M hdepth) ≪≫
    IsoPuncturePushforward.restrictFreeIso seriesPuncture.ι _

abbrev baseModelPuncture : V.Opens := completedBlowdown ⁻¹ᵁ seriesPuncture

/-- The required source framing, obtained from CM freeness and the puncture isomorphisms of both models. -/
def modelPushforwardFreeIso :
    (restrictFunctor baseModelPuncture.ι).obj (modelPushforward M) ≅
    SheafOfModules.free (basisIndex M hdepth) :=
  IsoPuncturePushforward.reflectFreeIso (completedBlowdown ∣_ seriesPuncture) _ _
    ((CoherentBaseChange.pushforwardRestrictIso completedBlowdown seriesPuncture
      (modelPushforward M)).symm ≪≫ overBasePunctureFreeIso M hdepth)
end SourceConeMorphism

end

noncomputable section
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace ActualOpenComparison
open Scheme.Modules
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N P : Y.Modules} (V : X.Opens) (W : Y.Opens) (h : f ''ᵁ V ≤ W)

/-- Pull a morphism on a target open to a chart open whose image it contains.
The scalar restriction uses the chart ring isomorphism. -/
def pullOverHom (a : M.over W ⟶ N.over W) :
    ((restrictFunctor f).obj M).over V ⟶ ((restrictFunctor f).obj N).over V where
  val := {
    app U := (ModuleCat.restrictScalars (f.appIso U.unop.left).inv.hom).map
      (a.val.app (op (Over.mk (homOfLE ((f.opensFunctor.monotone U.unop.hom.le).trans h)))))
    naturality {U U'} p := by
      ext x
      let q : Over.mk (homOfLE ((f.opensFunctor.monotone U'.unop.hom.le).trans h)) ⟶
          Over.mk (homOfLE ((f.opensFunctor.monotone U.unop.hom.le).trans h)) :=
        Over.homMk (f.opensFunctor.map p.unop.left) (by subsingleton)
      exact ConcreteCategory.congr_hom (a.val.naturality q.op) x }

lemma pullOverHom_id : pullOverHom f V W h (𝟙 (M.over W)) = 𝟙 _ := by
  rfl

lemma pullOverHom_comp (a : M.over W ⟶ N.over W) (b : N.over W ⟶ P.over W) :
    pullOverHom f V W h (a ≫ b) = pullOverHom f V W h a ≫ pullOverHom f V W h b := by
  rfl

/-- A puncture isomorphism restricts functorially to the puncture on every affine chart. -/
def pullOverIso (e : M.over W ≅ N.over W) :
    ((restrictFunctor f).obj M).over V ≅ ((restrictFunctor f).obj N).over V where
  hom := pullOverHom f V W h e.hom
  inv := pullOverHom f V W h e.inv
  hom_inv_id := by rw [← pullOverHom_comp, e.hom_inv_id, pullOverHom_id]
  inv_hom_id := by rw [← pullOverHom_comp, e.inv_hom_id, pullOverHom_id]

/-- Compatibility of a global morphism and this chart-open pullback. -/
lemma pullOverHom_global (a : M ⟶ N) :
    pullOverHom f V W h (a.over W) = ((restrictFunctor f).map a).over V := by
  rfl
end ActualOpenComparison

end

noncomputable section
namespace CartierAffineLattice
variable {R : Type*} [CommRing R]
  {M N L K : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L]
  [AddCommGroup K] [Module R K]

lemma regular_pow (t : R) (h : IsSMulRegular M t) (n : ℕ) :
    IsSMulRegular M (t ^ n) := by
  induction n with
  | zero =>
    intro x y hxy
    simpa only [pow_zero, one_smul] using hxy
  | succ n ih =>
    intro x y hxy
    apply ih
    apply h
    simpa only [pow_succ', mul_smul] using hxy

lemma injective_localization (t : R) (f : M →ₗ[R] L)
    [IsLocalizedModule.Away t f] (ht : IsSMulRegular M t) : Function.Injective f := by
  intro x y hxy
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq t hxy
  exact regular_pow t ht n hn

/-- Clearing denominators in an isomorphism of principal localizations of finitely
presented modules gives embeddings in both directions. Their composites are powers
of the Cartier equation, by localization of finite-presentation Hom. -/
lemma exists_sandwich [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (t : R) (htM : IsSMulRegular M t) (htN : IsSMulRegular N t)
    (f : M →ₗ[R] L) [IsLocalizedModule.Away t f]
    (g : N →ₗ[R] K) [IsLocalizedModule.Away t g] (e : L ≃ₗ[R] K) :
    ∃ (a : M →ₗ[R] N) (b : N →ₗ[R] M) (k : ℕ),
      Function.Injective a ∧ Function.Injective b ∧
      a.comp b = t ^ k • (LinearMap.id : N →ₗ[R] N) ∧
      b.comp a = t ^ k • (LinearMap.id : M →ₗ[R] M) := by
  obtain ⟨a, s, ha⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers t) g (e.toLinearMap.comp f)
  obtain ⟨b, u, hb⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers t) f (e.symm.toLinearMap.comp g)
  obtain ⟨s, n, rfl⟩ := s
  obtain ⟨u, m, rfl⟩ := u
  have haf (x : M) : g (a x) = t ^ n • e (f x) := LinearMap.congr_fun ha x
  have hbf (x : N) : f (b x) = t ^ m • e.symm (g x) := LinearMap.congr_fun hb x
  have hf := injective_localization t f htM
  have hg := injective_localization t g htN
  have hab : a.comp b = t ^ (n + m) • (LinearMap.id : N →ₗ[R] N) := by
    ext x
    apply hg
    change g (a (b x)) = g (t ^ (n + m) • x)
    rw [haf, hbf, map_smul, e.apply_symm_apply, map_smul, pow_add, mul_smul]
  have hba : b.comp a = t ^ (n + m) • (LinearMap.id : M →ₗ[R] M) := by
    ext x
    apply hf
    change f (b (a x)) = f (t ^ (n + m) • x)
    rw [hbf, haf, map_smul, e.symm_apply_apply, map_smul, pow_add, mul_smul]
    exact smul_comm _ _ _
  refine ⟨a, b, n + m, ?_, ?_, hab, hba⟩
  · intro x y hxy
    apply regular_pow t htM (n + m)
    have h := congrArg b hxy
    change (b.comp a) x = (b.comp a) y at h
    simpa only [hba, LinearMap.smul_apply, LinearMap.id_apply] using h
  · intro x y hxy
    apply regular_pow t htN (n + m)
    have h := congrArg a hxy
    change (a.comp b) x = (a.comp b) y at h
    simpa only [hab, LinearMap.smul_apply, LinearMap.id_apply] using h
end CartierAffineLattice


open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
namespace CartierAffineLattice
open Scheme.Modules
variable {R : CommRingCat.{0}}

/-- Restriction to a principal open supplies the localized-module
isomorphism used for clearing denominators. -/
def punctureSectionsIso {M N : (Spec R).Modules} (U : (Spec R).Opens)
    (e : M.over U ≅ N.over U) : Γ(M, U) ≃ₗ[R] Γ(N, U) := by
  let q : Γ(M, U) ≃ₗ[Γ(Spec R, U)] Γ(N, U) :=
    ((SheafOfModules.evaluation _ (op (Over.mk (𝟙 U)))).mapIso e).toLinearEquiv
  exact q.restrictScalars R

/-- On an affine Cartier chart the lattice embeddings are obtained from
a punctured sheaf isomorphism, rather than supplied as hypotheses. -/
lemma exists_sandwich_of_puncture
    (M N : ModuleCat R) [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (t : R) (htM : IsSMulRegular M t) (htN : IsSMulRegular N t)
    (e : (tilde M).over (PrimeSpectrum.basicOpen t) ≅
      (tilde N).over (PrimeSpectrum.basicOpen t)) :
    ∃ (a : M →ₗ[R] N) (b : N →ₗ[R] M) (k : ℕ),
      Function.Injective a ∧ Function.Injective b ∧
      a.comp b = t ^ k • (LinearMap.id : N →ₗ[R] N) ∧
      b.comp a = t ^ k • (LinearMap.id : M →ₗ[R] M) :=
  exists_sandwich t htM htN (tilde.toOpen M (PrimeSpectrum.basicOpen t)).hom
    (tilde.toOpen N (PrimeSpectrum.basicOpen t)).hom (punctureSectionsIso _ e)

/-- The constructed sandwich kills the cokernel by the same power. -/
lemma sandwich_annihilates_quotient {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (a : M →ₗ[R] N) (b : N →ₗ[R] M) (t : R) (k : ℕ)
    (hab : a.comp b = t ^ k • (LinearMap.id : N →ₗ[R] N)) :
    ∀ q : N ⧸ a.range, t ^ k • q = 0 := by
  intro q
  induction q using Quotient.inductionOn' with
  | h x =>
    change a.range.mkQ (t ^ k • x) = 0
    apply (Submodule.Quotient.mk_eq_zero a.range).mpr
    refine ⟨b x, ?_⟩
    exact LinearMap.congr_fun hab x
end CartierAffineLattice

end

noncomputable section
namespace CartierAffineLattice
variable {R : Type*} [CommRing R]
  {M N L K : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L]
  [AddCommGroup K] [Module R K]

/-- The cleared maps agree with the prescribed puncture isomorphism
after multiplication by a shared denominator. -/
lemma exists_compatible_sandwich
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (t : R) (htM : IsSMulRegular M t) (htN : IsSMulRegular N t)
    (f : M →ₗ[R] L) [IsLocalizedModule.Away t f]
    (g : N →ₗ[R] K) [IsLocalizedModule.Away t g] (e : L ≃ₗ[R] K) :
    ∃ (n : ℕ) (a : M →ₗ[R] N) (b : N →ₗ[R] M),
      Function.Injective a ∧ Function.Injective b ∧
      (∀ x, g (a x) = t ^ n • e (f x)) ∧
      (∀ y, f (b y) = t ^ n • e.symm (g y)) ∧
      a.comp b = t ^ (2 * n) • (LinearMap.id : N →ₗ[R] N) ∧
      b.comp a = t ^ (2 * n) • (LinearMap.id : M →ₗ[R] M) := by
  obtain ⟨a₀, s, ha⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers t) g (e.toLinearMap.comp f)
  obtain ⟨b₀, u, hb⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers t) f (e.symm.toLinearMap.comp g)
  obtain ⟨s, i, rfl⟩ := s
  obtain ⟨u, j, rfl⟩ := u
  have ha₀ (x : M) : g (a₀ x) = t ^ i • e (f x) := LinearMap.congr_fun ha x
  have hb₀ (y : N) : f (b₀ y) = t ^ j • e.symm (g y) := LinearMap.congr_fun hb y
  let a : M →ₗ[R] N := t ^ j • a₀
  let b : N →ₗ[R] M := t ^ i • b₀
  have haf (x : M) : g (a x) = t ^ (i + j) • e (f x) := by
    change g (t ^ j • a₀ x) = _
    rw [map_smul, ha₀ x, pow_add, mul_smul]
    exact smul_comm _ _ _
  have hbf (y : N) : f (b y) = t ^ (i + j) • e.symm (g y) := by
    change f (t ^ i • b₀ y) = _
    rw [map_smul, hb₀ y, pow_add, mul_smul]
  have hf := injective_localization t f htM
  have hg := injective_localization t g htN
  have hab : a.comp b = t ^ (2 * (i + j)) • (LinearMap.id : N →ₗ[R] N) := by
    ext y
    apply hg
    change g (a (b y)) = g (t ^ (2 * (i + j)) • y)
    simp only [haf, hbf, map_smul, e.apply_symm_apply, two_mul, pow_add, mul_smul]
  have hba : b.comp a = t ^ (2 * (i + j)) • (LinearMap.id : M →ₗ[R] M) := by
    ext x
    apply hf
    change f (b (a x)) = f (t ^ (2 * (i + j)) • x)
    simp only [hbf, haf, map_smul, e.symm_apply_apply, two_mul, pow_add, mul_smul]
  refine ⟨i + j, a, b, ?_, ?_, haf, hbf, hab, hba⟩
  · intro x y hxy
    apply regular_pow t htM (2 * (i + j))
    have h := congrArg b hxy
    change (b.comp a) x = (b.comp a) y at h
    simpa only [hba, LinearMap.smul_apply, LinearMap.id_apply] using h
  · intro x y hxy
    apply regular_pow t htN (2 * (i + j))
    have h := congrArg a hxy
    change (a.comp b) x = (a.comp b) y at h
    simpa only [hab, LinearMap.smul_apply, LinearMap.id_apply] using h

/-- A cleared extension of a puncture morphism is unique
when the Cartier equation acts regularly on the target. -/
lemma cleared_extension_unique (t : R) (htN : IsSMulRegular N t)
    (g : N →ₗ[R] K) [IsLocalizedModule.Away t g]
    (a b : M →ₗ[R] N) (h : g.comp a = g.comp b) : a = b := by
  ext x
  exact injective_localization t g htN (LinearMap.congr_fun h x)
end CartierAffineLattice


open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
open Scheme.Modules
namespace AffineNaturalScalar
variable (R : CommRingCat.{0}) (b : 𝟭 (Spec R).Modules ⟶ 𝟭 (Spec R).Modules)

/-- The scalar of a natural endomorphism on affine module sheaves. -/
def scalar : R := ((tilde.functor R).preimage (b.app (tilde (ModuleCat.of R R)))) 1

/-- Naturality against the cyclic maps from the structure module forces the
affine endomorphism to be scalar multiplication on every module. -/
lemma preimage_apply (M : ModuleCat R) (m : M) :
    ((tilde.functor R).preimage (b.app (tilde M))) m = scalar R b • m := by
  let F := tilde.functor R
  change (F.preimage (b.app (F.obj M))) m = _
  let g : ModuleCat.of R R ⟶ M := ModuleCat.ofHom (LinearMap.toSpanSingleton R M m)
  have h : g ≫ F.preimage (b.app (F.obj M)) =
      F.preimage (b.app (F.obj (ModuleCat.of R R))) ≫ g := by
    apply F.map_injective
    simp only [Functor.map_comp, F.map_preimage]
    simpa only [Functor.id_map] using b.naturality (F.map g)
  have hh := congrArg (fun k : ModuleCat.of R R ⟶ M => k 1) h
  change F.preimage (b.app (F.obj M)) ((1 : R) • m) =
    (F.preimage (b.app (F.obj (ModuleCat.of R R))) 1) • m at hh
  change F.preimage (b.app (F.obj M)) m =
    (F.preimage (b.app (F.obj (ModuleCat.of R R))) 1) • m
  simpa only [one_smul] using hh

lemma preimage_eq (M : ModuleCat R) :
    (tilde.functor R).preimage (b.app (tilde M)) =
      ModuleCat.ofHom (scalar R b • (LinearMap.id : M →ₗ[R] M)) := by
  apply ModuleCat.hom_ext
  ext m
  exact preimage_apply R b M m

/-- Uniform scalar nilpotence of an affine module implies
nilpotence of the corresponding sheaf endomorphism. -/
lemma power_zero (M : ModuleCat R) (n : ℕ)
    (h : ∀ m : M, scalar R b ^ n • m = 0) :
    (End.of (b.app (tilde M)) ^ n).asHom = 0 := by
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
  have hz : (a ^ n).asHom = 0 := by
    apply ModuleCat.hom_ext
    ext m
    exact (ha n m).trans (h m)
  change (End.of (b.app (F.obj M)) ^ n).asHom = 0
  have hf : End.of (b.app (F.obj M)) = (Functor.mapEnd M F) a := by
    exact (F.map_preimage (b.app (tilde M))).symm
  calc
    (End.of (b.app (F.obj M)) ^ n).asHom = ((Functor.mapEnd M F) a ^ n).asHom :=
      congrArg (fun z : End (F.obj M) => (z ^ n).asHom) hf
    _ = ((Functor.mapEnd M F) (a ^ n)).asHom :=
      congrArg End.asHom ((Functor.mapEnd M F).map_pow a n).symm
    _ = F.map ((a ^ n).asHom) := rfl
    _ = 0 := by rw [hz, Functor.map_zero]
end AffineNaturalScalar

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

private local instance unitSectionSMul (M : SheafOfModules.{u} (ringSheaf R))
    (U : Cᵒᵖ) : SMul ((SheafOfModules.unit (ringSheaf R)).val.obj U) (M.val.obj U) :=
  show SMul (R.obj.obj U) (M.val.obj U) from (M.val.obj U).isModule.toSMul

/-- The tensor functor trivialization of a trivial line. -/
def trivialTensorIso {L : SheafOfModules.{u} (ringSheaf R)}
    (e : L ≅ SheafOfModules.unit _) : tensorLeft R L ≅ 𝟭 _ :=
  tensorLeftIso R e ≪≫ tensorUnitLeftIso R

lemma trivialTensorIso_pure {L : SheafOfModules.{u} (ringSheaf R)}
    (e : L ≅ SheafOfModules.unit _) (M : SheafOfModules.{u} (ringSheaf R))
    (U : Cᵒᵖ) (l : L.val.obj U) (m : M.val.obj U) :
    ((trivialTensorIso R e).hom.app M).val.app U (pure R L M U l m) =
      (e.hom.val.app U l) • m := by
  change (leftUnitIso R M).hom.val.app U
    (((tensorLeftMap R e.hom).app M).val.app U (pure R L M U l m)) = _
  rw [tensorLeftMap_pure]
  erw [leftUnitIso_pure]
  rfl

/-- Normalizing a line-ideal action by a trivialization is
multiplication by the principal equation, on every section module. -/
lemma trivial_action_eq_smul {L : SheafOfModules.{u} (ringSheaf R)}
    (e : L ≅ SheafOfModules.unit _) (i : L ⟶ SheafOfModules.unit _)
    (M : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ) (m : M.val.obj U) :
    (((trivialTensorIso R e).inv ≫ idealAction R i).app M).val.app U m =
      (i.val.app U (e.inv.val.app U (1 : R.obj.obj U))) • m := by
  let : Module (R.obj.obj U) (M.val.obj U) := (M.val.obj U).isModule
  let x := pure R L M U (e.inv.val.app U (1 : R.obj.obj U)) m
  have hx : ((trivialTensorIso R e).hom.app M).val.app U x = m := by
    rw [trivialTensorIso_pure]
    have he := congrArg (fun f : SheafOfModules.unit (ringSheaf R) ⟶ SheafOfModules.unit (ringSheaf R) =>
      f.val.app U (1 : R.obj.obj U)) e.inv_hom_id
    change e.hom.val.app U (e.inv.val.app U (1 : R.obj.obj U)) = (1 : R.obj.obj U) at he
    rw [he]
    change (1 : R.obj.obj U) • m = m
    exact one_smul _ _
  rw [← hx]
  have he := congrArg (fun f : (tensorLeft R L).obj M ⟶ M =>
    f.val.app U x) ((trivialTensorIso R e).hom_inv_id_app_assoc M
      ((idealAction R i).app M))
  change (((trivialTensorIso R e).inv ≫ idealAction R i).app M).val.app U
    (((trivialTensorIso R e).hom.app M).val.app U x) =
      ((idealAction R i).app M).val.app U x at he
  rw [he, hx]
  exact idealAction_pure R i M U (e.inv.val.app U (1 : R.obj.obj U)) m

/-- On the structure sheaf, the normalized tensor action is the trivialized ideal inclusion. -/
lemma trivial_action_unit {L : SheafOfModules.{u} (ringSheaf R)}
    (e : L ≅ SheafOfModules.unit _) (i : L ⟶ SheafOfModules.unit _) :
    ((trivialTensorIso R e).inv ≫ idealAction R i).app (SheafOfModules.unit _) =
      e.inv ≫ i := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (((trivialTensorIso R e).inv ≫ idealAction R i).app
    (SheafOfModules.unit _)).val.app U r = i.val.app U (e.inv.val.app U r)
  rw [trivial_action_eq_smul]
  let f : R.obj.obj U →ₗ[R.obj.obj U] R.obj.obj U := ((e.inv ≫ i).val.app U).hom
  have hf (x : R.obj.obj U) : f x = x * f 1 := by
    simpa only [smul_eq_mul, mul_one] using f.map_smul x (1 : R.obj.obj U)
  let r' : R.obj.obj U := r
  change f 1 * r' = f r'
  exact (mul_comm (f 1) r').trans (hf r').symm

end ActualSheafTensor

end


/-! The Grothendieck group of an abelian category and the Euler identity
for restriction minus first Tor in the Cartier restriction formula. -/

open CategoryTheory CategoryTheory.Limits

namespace CoherentK0
universe v u
variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The two usual relations: isomorphic objects have the same class, and
short exact sequences are additive. -/
def relations : Set (FreeAbelianGroup C) :=
  {z | (∃ S : ShortComplex C, S.ShortExact ∧
      z = FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) ∨
    (∃ X Y : C, Nonempty (X ≅ Y) ∧ z = FreeAbelianGroup.of X - FreeAbelianGroup.of Y)}

/-- Grothendieck group of the exact category underlying an abelian category. -/
def Group := FreeAbelianGroup C ⧸ AddSubgroup.closure (relations C)

noncomputable instance : AddCommGroup (Group C) :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup C ⧸ AddSubgroup.closure (relations C)))

variable {C}

noncomputable def cls (X : C) : Group C := QuotientAddGroup.mk (FreeAbelianGroup.of X)

lemma cls_iso {X Y : C} (e : X ≅ Y) : cls X = cls Y := by
  apply sub_eq_zero.mp
  change (QuotientAddGroup.mk (FreeAbelianGroup.of X - FreeAbelianGroup.of Y) : Group C) = 0
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact AddSubgroup.subset_closure (Or.inr ⟨X, Y, ⟨e⟩, rfl⟩)

lemma cls_shortExact {S : ShortComplex C} (hS : S.ShortExact) :
    cls S.X₂ = cls S.X₁ + cls S.X₃ := by
  have h : (QuotientAddGroup.mk (FreeAbelianGroup.of S.X₂ -
      FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) : Group C) = 0 := by
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact AddSubgroup.subset_closure (Or.inl ⟨S, hS, rfl⟩)
  change cls S.X₂ - cls S.X₁ - cls S.X₃ = 0 at h
  calc
    cls S.X₂ = (cls S.X₂ - cls S.X₁ - cls S.X₃) + (cls S.X₁ + cls S.X₃) := by abel
    _ = cls S.X₁ + cls S.X₃ := by rw [h, zero_add]

/-- The class of an exact triple is the sum of the classes of its two images. -/
lemma cls_exact {S : ShortComplex C} (hS : S.Exact) :
    cls S.X₂ = cls (Abelian.image S.f) + cls (Abelian.image S.g) := by
  let T := ShortComplex.mk (Abelian.image.ι S.f) S.g
    (Abelian.image_ι_comp_eq_zero S.zero)
  have hT : T.Exact := S.exact_iff_exact_image_ι.mp hS
  let U := ShortComplex.mk T.f (Abelian.coimage.π T.g)
    (Abelian.comp_coimage_π_eq_zero T.zero)
  have hU : U.ShortExact := ⟨T.exact_iff_exact_coimage_π.mp hT⟩
  have h := cls_shortExact hU
  change cls S.X₂ = cls (Abelian.image S.f) + cls (Abelian.coimage S.g) at h
  rw [cls_iso (Abelian.coimageIsoImage S.g)] at h
  exact h

lemma cls_image_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    cls X = cls (Abelian.image f) := by
  have : IsIso (Abelian.factorThruImage f) := isIso_of_mono_of_epi _
  exact cls_iso (asIso (Abelian.factorThruImage f))

lemma cls_image_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    cls (Abelian.image f) = cls Y := by
  have : Epi (Abelian.image.ι f) := epi_of_epi_fac (Abelian.image.fac f)
  have : IsIso (Abelian.image.ι f) := isIso_of_mono_of_epi _
  exact cls_iso (asIso (Abelian.image.ι f))

/-- Six-term exactness gives the Euler identity for restriction minus first Tor. -/
lemma six_term_euler {A B K P Q T : C}
    (f : A ⟶ B) (g : B ⟶ K) (δ : K ⟶ P) (h : P ⟶ Q) (i : Q ⟶ T)
    [Mono f] [Epi i]
    (z₁ : f ≫ g = 0) (z₂ : g ≫ δ = 0) (z₃ : δ ≫ h = 0) (z₄ : h ≫ i = 0)
    (e₁ : (ShortComplex.mk f g z₁).Exact)
    (e₂ : (ShortComplex.mk g δ z₂).Exact)
    (e₃ : (ShortComplex.mk δ h z₃).Exact)
    (e₄ : (ShortComplex.mk h i z₄).Exact) :
    cls Q - cls B = (cls P - cls A) + (cls T - cls K) := by
  have hB := cls_exact e₁
  have hK := cls_exact e₂
  have hP := cls_exact e₃
  have hQ := cls_exact e₄
  change cls B = cls (Abelian.image f) + cls (Abelian.image g) at hB
  change cls K = cls (Abelian.image g) + cls (Abelian.image δ) at hK
  change cls P = cls (Abelian.image δ) + cls (Abelian.image h) at hP
  change cls Q = cls (Abelian.image h) + cls (Abelian.image i) at hQ
  rw [hB, hK, hP, hQ, cls_image_of_mono f, ← cls_image_of_epi i]
  abel

/-- The snake lemma gives the Euler identity for the kernel and cokernel rows. -/
lemma snake_euler (S : ShortComplex.SnakeInput C) [Mono S.L₁.f] [Epi S.L₂.g] :
    cls S.L₃.X₂ - cls S.L₀.X₂ =
      (cls S.L₃.X₁ - cls S.L₀.X₁) + (cls S.L₃.X₃ - cls S.L₀.X₃) :=
  six_term_euler S.L₀.f S.L₀.g S.δ S.L₃.f S.L₃.g
    S.L₀.zero S.L₀_g_δ S.δ_L₃_f S.L₃.zero
    S.L₀_exact S.L₁'_exact S.L₂'_exact S.L₃_exact

end CoherentK0


namespace CoherentK0
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- The snake Euler identity descends to the divisor category:
fullness lifts the connecting morphism and faithfulness reflects exactness. -/
lemma snake_euler_in_divisor
    (J : D ⥤ C) [J.Full] [J.Faithful] [J.PreservesZeroMorphisms]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (K Q : ShortComplex D) (S₁ S₂ : ShortComplex C)
    (i : K.map J ⟶ S₁) (m : S₁ ⟶ S₂) (p : S₂ ⟶ Q.map J)
    (wi : i ≫ m = 0) (wp : m ≫ p = 0)
    (hi : IsLimit (KernelFork.ofι i wi))
    (hp : IsColimit (CokernelCofork.ofπ p wp))
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) :
    cls Q.X₂ - cls K.X₂ =
      (cls Q.X₁ - cls K.X₁) + (cls Q.X₃ - cls K.X₃) := by
  let S : ShortComplex.SnakeInput C :=
    { L₀ := K.map J, L₁ := S₁, L₂ := S₂, L₃ := Q.map J
      v₀₁ := i, v₁₂ := m, v₂₃ := p, w₀₂ := wi, w₁₃ := wp
      h₀ := hi, h₃ := hp, L₁_exact := h₁.exact, epi_L₁_g := h₁.epi_g
      L₂_exact := h₂.exact, mono_L₂_f := h₂.mono_f }
  have : Mono S.L₁.f := h₁.mono_f
  have : Epi S.L₂.g := h₂.epi_g
  let δ : K.X₃ ⟶ Q.X₁ := J.preimage S.δ
  have mapδ : J.map δ = S.δ := J.map_preimage _
  have z₂ : K.g ≫ δ = 0 := by
    apply J.map_injective
    rw [J.map_comp, J.map_zero, mapδ]
    exact S.L₀_g_δ
  have z₃ : δ ≫ Q.f = 0 := by
    apply J.map_injective
    rw [J.map_comp, J.map_zero, mapδ]
    exact S.δ_L₃_f
  have e₁ : K.Exact := (K.exact_map_iff_of_faithful J).mp S.L₀_exact
  have e₄ : Q.Exact := (Q.exact_map_iff_of_faithful J).mp S.L₃_exact
  have e₂ : (ShortComplex.mk K.g δ z₂).Exact := by
    apply ((ShortComplex.mk K.g δ z₂).exact_map_iff_of_faithful J).mp
    exact ShortComplex.exact_of_iso
      (ShortComplex.isoMk (S₁ := S.L₁') (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by change 𝟙 (J.obj K.X₂) ≫ J.map K.g = J.map K.g ≫ 𝟙 (J.obj K.X₃)
            simp)
        (by change 𝟙 (J.obj K.X₃) ≫ J.map δ = S.δ ≫ 𝟙 (J.obj Q.X₁)
            exact (Category.id_comp _).trans (mapδ.trans (Category.comp_id _).symm))) S.L₁'_exact
  have e₃ : (ShortComplex.mk δ Q.f z₃).Exact := by
    apply ((ShortComplex.mk δ Q.f z₃).exact_map_iff_of_faithful J).mp
    exact ShortComplex.exact_of_iso
      (ShortComplex.isoMk (S₁ := S.L₂') (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by change 𝟙 (J.obj K.X₃) ≫ J.map δ = S.δ ≫ 𝟙 (J.obj Q.X₁)
            exact (Category.id_comp _).trans (mapδ.trans (Category.comp_id _).symm))
        (by change 𝟙 (J.obj Q.X₁) ≫ J.map Q.f = J.map Q.f ≫ 𝟙 (J.obj Q.X₂)
            simp)) S.L₂'_exact
  have : Mono K.f := J.mono_of_mono_map (S.mono_L₀_f)
  have : Epi Q.g := J.epi_of_epi_map (S.epi_L₃_g)
  exact six_term_euler K.f K.g δ Q.f Q.g K.zero z₂ z₃ Q.zero e₁ e₂ e₃ e₄

end CoherentK0

namespace CoherentK0
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- Restriction minus first Tor is additive for a length-one Cartier resolution. -/
lemma cartier_restriction_additive
    (J : D ⥤ C) [J.Full] [J.Faithful] [J.PreservesZeroMorphisms]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (T : C ⥤ C) [T.PreservesZeroMorphisms]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (K Q : C ⥤ D) [K.PreservesZeroMorphisms] [Q.PreservesZeroMorphisms]
    (κ : K ⋙ J ⟶ T) (ε : T ⟶ 𝟭 C) (π : 𝟭 C ⟶ Q ⋙ J)
    (zK : κ ≫ ε = 0) (zQ : ε ≫ π = 0)
    (hK : ∀ X, IsLimit (KernelFork.ofι (κ.app X) (NatTrans.congr_app zK X)))
    (hQ : ∀ X, IsColimit (CokernelCofork.ofπ (π.app X) (NatTrans.congr_app zQ X)))
    {S : ShortComplex C} (hS : S.ShortExact) :
    cls (Q.obj S.X₂) - cls (K.obj S.X₂) =
      (cls (Q.obj S.X₁) - cls (K.obj S.X₁)) +
      (cls (Q.obj S.X₃) - cls (K.obj S.X₃)) := by
  let i := S.mapNatTrans κ
  let m := S.mapNatTrans ε
  let p := S.mapNatTrans π
  have wi : i ≫ m = 0 := by
    ext <;> exact NatTrans.congr_app zK _
  have wp : m ≫ p = 0 := by
    ext <;> exact NatTrans.congr_app zQ _
  have hi : IsLimit (KernelFork.ofι i wi) := by
    apply ShortComplex.isLimitOfIsLimitπ
    · refine (isLimitMapConeForkEquiv' ShortComplex.π₁ wi).symm ?_
      exact hK S.X₁
    · refine (isLimitMapConeForkEquiv' ShortComplex.π₂ wi).symm ?_
      exact hK S.X₂
    · refine (isLimitMapConeForkEquiv' ShortComplex.π₃ wi).symm ?_
      exact hK S.X₃
  have hp : IsColimit (CokernelCofork.ofπ p wp) := by
    apply ShortComplex.isColimitOfIsColimitπ
    · refine (isColimitMapCoconeCoforkEquiv' ShortComplex.π₁ wp).symm ?_
      exact hQ S.X₁
    · refine (isColimitMapCoconeCoforkEquiv' ShortComplex.π₂ wp).symm ?_
      exact hQ S.X₂
    · refine (isColimitMapCoconeCoforkEquiv' ShortComplex.π₃ wp).symm ?_
      exact hQ S.X₃
  exact snake_euler_in_divisor J (S.map K) (S.map Q) (S.map T) S
    i m p wi wp hi hp (hS.map_of_exact T) hS

end CoherentK0

namespace CoherentK0
open scoped ZeroObject
universe v u w
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma cls_zero : cls (0 : C) = 0 := by
  let S : ShortComplex C := ShortComplex.mk (𝟙 (0 : C)) (𝟙 (0 : C))
    ((isZero_zero C).eq_of_src _ _)
  have hS : S.ShortExact := ⟨S.exact_of_isZero_X₂ (isZero_zero C)⟩
  have h := cls_shortExact hS
  change cls (0 : C) = cls (0 : C) + cls (0 : C) at h
  apply add_left_cancel (a := cls (0 : C))
  simpa using h.symm

lemma cls_isZero {X : C} (hX : IsZero X) : cls X = 0 := by
  rw [cls_iso hX.isoZero, cls_zero]

/-- The universal property of the Grothendieck group. In particular a Chern
character must be invariant under isomorphism and additive on
short exact sequences before this construction can be used. -/
noncomputable def lift {A : Type w} [AddCommGroup A] (f : C → A)
    (hi : ∀ {X Y : C}, (X ≅ Y) → f X = f Y)
    (he : ∀ {S : ShortComplex C}, S.ShortExact → f S.X₂ = f S.X₁ + f S.X₃) :
    Group C →+ A :=
  QuotientAddGroup.lift (AddSubgroup.closure (relations C)) (FreeAbelianGroup.lift f) (by
    apply (AddSubgroup.closure_le _).mpr
    rintro z (⟨S, hS, rfl⟩ | ⟨X, Y, ⟨e⟩, rfl⟩)
    · change (FreeAbelianGroup.lift f) (FreeAbelianGroup.of S.X₂ -
        FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
      simp only [map_sub, FreeAbelianGroup.lift_apply_of]
      rw [he hS]
      abel
    · change (FreeAbelianGroup.lift f) (FreeAbelianGroup.of X - FreeAbelianGroup.of Y) = 0
      simp only [map_sub, FreeAbelianGroup.lift_apply_of]
      exact sub_eq_zero.mpr (hi e))

@[simp] lemma lift_cls {A : Type w} [AddCommGroup A] (f : C → A)
    (hi : ∀ {X Y : C}, (X ≅ Y) → f X = f Y)
    (he : ∀ {S : ShortComplex C}, S.ShortExact → f S.X₂ = f S.X₁ + f S.X₃)
    (X : C) : lift f hi he (cls X) = f X := by
  exact FreeAbelianGroup.lift_apply_of f X

/-- A finite filtration specified by short exact sequences,
with a list recording its successive quotients. -/
inductive FilteredBy : C → List C → Prop
  | zero (X : C) (hX : IsZero X) : FilteredBy X []
  | step {S : ShortComplex C} (hS : S.ShortExact) {qs : List C}
      (h : FilteredBy S.X₁ qs) : FilteredBy S.X₂ (S.X₃ :: qs)

lemma cls_filteredBy {X : C} {qs : List C} (h : FilteredBy X qs) :
    cls X = (qs.map cls).sum := by
  induction h with
  | zero X hX => simpa using cls_isZero hX
  | @step S hS qs h ih =>
    rw [cls_shortExact hS, ih]
    simp only [List.map_cons, List.sum_cons]
    exact add_comm _ _

/-- The filtration theorem after any additive invariant. -/
lemma map_cls_filteredBy {A : Type w} [AddCommGroup A] (φ : Group C →+ A)
    {X : C} {qs : List C} (h : FilteredBy X qs) :
    φ (cls X) = (qs.map fun Q => φ (cls Q)).sum := by
  rw [cls_filteredBy h, map_list_sum, List.map_map]
  rfl

end CoherentK0

end OAI
