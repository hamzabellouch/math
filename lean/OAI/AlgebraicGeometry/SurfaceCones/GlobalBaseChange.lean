import OAI.AlgebraicGeometry.SurfaceCones.ClosedChartBaseChange

namespace OAI

/-! Closed base change between the zero sections, obtained from the canonical affine mates by
pasting and descent along the affine cover. -/
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

lemma completedClosedChart_mate_isIso (i : Fin 3)
    (M : (Spec (.of (completedSourceChart i))).Modules) [M.IsQuasicoherent] :
    IsIso ((mate (completedProjection i) (completedPlaneZeroChart i) (completedZeroChart i)
      (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))
      (completedClosedChart_commute i)).app M) := by
  exact AffineClosedBaseChange.sheafMate_isIso _ _ _ _ (completedClosedChart_isPushout i) M

lemma open_pullback_qc {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i]
    (M : Y.Modules) [M.IsQuasicoherent] : ((Scheme.Modules.pullback i).obj M).IsQuasicoherent := by
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback i).app M) inferInstance

lemma actualMate_chart_isIso (M : W.Modules) [M.IsQuasicoherent] (i : Fin 3) :
    IsIso ((Scheme.Modules.pullback (planeIota i)).map
      ((mate g completedPlaneZero completedSourceZero ExplicitCone.projectiveNormalization
        completedSourceZero_g).app M)) := by
  have Ho : IsIso ((mate g (completedBlowupIota i) (completedIota i) (completedProjection i)
      (completedIota_projection i)).app M) :=
    openCartesianMate_isIso _ _ _ _ (completedProjection_isPullback i) M
  have : ((Scheme.Modules.pullback (completedIota i)).obj M).IsQuasicoherent :=
    open_pullback_qc _ M
  have Hc := completedClosedChart_mate_isIso i ((Scheme.Modules.pullback (completedIota i)).obj M)
  have Hp := pasted_mate_isIso g (completedBlowupIota i) (completedIota i)
    (completedProjection i) (completedIota_projection i)
    (completedPlaneZeroChart i) (completedZeroChart i)
    (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i))) (completedClosedChart_commute i) M
  have Hp' : IsIso ((mate g ((planeIota i) ≫ completedPlaneZero)
      ((surfaceIota i) ≫ completedSourceZero)
      (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))
      (paste_comm g completedPlaneZero completedSourceZero ExplicitCone.projectiveNormalization
        completedSourceZero_g (planeIota i) (surfaceIota i)
        (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i))) (surface_chart_square i))).app M) := by
    exact (mate_isIso_congr _ _ _ _ _ M
      (planeIota_completedPlaneZero i).symm (surfaceIota_completedSourceZero i).symm _).mp Hp
  have Hs := openCartesianMate_isIso ExplicitCone.projectiveNormalization (planeIota i)
    (surfaceIota i) (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i)))
    (surface_isPullback i) ((Scheme.Modules.pullback completedSourceZero).obj M)
  exact map_mate_of_pasted_isIso g completedPlaneZero completedSourceZero
    ExplicitCone.projectiveNormalization completedSourceZero_g (planeIota i) (surfaceIota i)
    (Spec.map (CommRingCat.ofHom (surfaceDirectionMap i))) (surface_chart_square i) M

lemma actualMate_isIso (M : W.Modules) [M.IsQuasicoherent] :
    IsIso ((mate g completedPlaneZero completedSourceZero ExplicitCone.projectiveNormalization
      completedSourceZero_g).app M) := by
  let φ := (mate g completedPlaneZero completedSourceZero ExplicitCone.projectiveNormalization
    completedSourceZero_g).app M
  apply CoherentGlobal.isIso_of_open_cover (fun i : Fin 3 => (planeIota i).opensRange)
    planeCover.iSup_opensRange φ
  intro i
  have hi := actualMate_chart_isIso M i
  have hr : IsIso ((restrictFunctor (planeIota i)).map φ) := by
    exact ((NatIso.isIso_map_iff (restrictFunctorIsoPullback (planeIota i)) φ)).mpr hi
  let e := (restrictFunctorComp (planeIota i).isoOpensRange.inv (planeIota i)).symm ≪≫
    restrictFunctorCongr (Scheme.Hom.isoOpensRange_inv_comp (planeIota i))
  have hx : IsIso (((restrictFunctor (planeIota i)) ⋙
      restrictFunctor (planeIota i).isoOpensRange.inv).map φ) := by
    change IsIso ((restrictFunctor (planeIota i).isoOpensRange.inv).map
      ((restrictFunctor (planeIota i)).map φ))
    infer_instance
  exact ((NatIso.isIso_map_iff e φ)).mp hx

def actualClosedBaseChangeIso (M : W.Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback completedPlaneZero).obj ((pushforward g).obj M) ≅
      (pushforward ExplicitCone.projectiveNormalization).obj
        ((Scheme.Modules.pullback completedSourceZero).obj M) := by
  have := actualMate_isIso M
  exact asIso ((mate g completedPlaneZero completedSourceZero ExplicitCone.projectiveNormalization
    completedSourceZero_g).app M)
end SourcePullbackChart

end

end OAI
