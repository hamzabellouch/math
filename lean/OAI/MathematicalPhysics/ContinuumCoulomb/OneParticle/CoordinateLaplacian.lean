import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.WeakH1Laplacian
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitPullback

namespace OAI

/-! Coordinate identities for the actual three-dimensional Laplacian. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

private def directionalSecond {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (e x : E) : ℝ := fderiv ℝ (fun y => fderiv ℝ f y e) x e

private theorem directionalSecond_affine {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] F) (c : F) (e x : E) :
    directionalSecond (fun y => f (L y+c)) e x = directionalSecond f (L e) (L x+c) := by
  have hfirst (y : E) : fderiv ℝ (fun z => f (L z+c)) y e =
      fderiv ℝ f (L y+c) (L e) := by
    exact congrArg (fun M : E →L[ℝ] ℝ => M e)
      (((hf.differentiable (by norm_num) _).hasFDerivAt).comp y
        (L.hasFDerivAt.add_const c)).fderiv
  have hd : ContDiff ℝ 1 (fun y => fderiv ℝ f y (L e)) :=
    (hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)).clm_apply contDiff_const
  unfold directionalSecond
  simp_rw [hfirst]
  exact congrArg (fun M : E →L[ℝ] ℝ => M e)
    (((hd.differentiable (by norm_num) _).hasFDerivAt).comp x
      (L.hasFDerivAt.add_const c)).fderiv

private theorem split_planar_second (f : SplitPosition → ℝ) (hf : ContDiff ℝ 2 f)
    (a : Fin 2) (p : SplitPosition) :
    planarPartial (planarPartial (fun r => f (r,p.2)) (planarAxis a)) (planarAxis a) p.1 =
      directionalSecond f (planarAxis a,0) p := by
  change directionalSecond (fun r => f (r,p.2)) (planarAxis a) p.1 = _
  have h := directionalSecond_affine f hf
    (ContinuousLinearMap.inl ℝ PlanarPosition ℝ) (0,p.2) (planarAxis a) p.1
  simpa only [ContinuousLinearMap.inl_apply,
    Prod.mk_add_mk, add_zero, zero_add] using h

private theorem split_vertical_second (f : SplitPosition → ℝ) (hf : ContDiff ℝ 2 f)
    (p : SplitPosition) :
    deriv (deriv (fun z => f (p.1,z))) p.2 = directionalSecond f (0,1) p := by
  have h := directionalSecond_affine f hf
    (ContinuousLinearMap.inr ℝ PlanarPosition ℝ) (p.1,0) 1 p.2
  simpa only [directionalSecond, fderiv_apply_one_eq_deriv, ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk, add_zero, zero_add] using h

theorem oneElectron_split_laplacian (f : SplitPosition → ℝ) (hf : ContDiff ℝ 2 f)
    (x : Configuration 1) :
    configurationRealLaplacian (fun y => f (positionSplitCoordinates (oneElectronCoordinates y))) x =
      splitLaplacian f (positionSplitCoordinates (oneElectronCoordinates x)) := by
  let L : Configuration 1 →L[ℝ] SplitPosition :=
    positionSplitCoordinates.toContinuousLinearMap.comp oneElectronCoordinates.toContinuousLinearEquiv.toContinuousLinearMap
  have hs (a : Fin 3) :
      directionalSecond (fun y => f (positionSplitCoordinates (oneElectronCoordinates y)))
        (EuclideanSpace.single (0,a) 1) x =
      directionalSecond f (positionSplitCoordinates (EuclideanSpace.single a 1))
        (positionSplitCoordinates (oneElectronCoordinates x)) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, oneElectronCoordinates_single, add_zero, L] using
      directionalSecond_affine f hf L 0 (EuclideanSpace.single (0,a) 1) x
  have hp (a : Fin 2) : positionSplitCoordinates (EuclideanSpace.single (Fin.castSucc a) 1) =
      (planarAxis a,0) := by
    rw [← splitCoordinate_planar_axis, ContinuousLinearEquiv.apply_symm_apply]
  have hz : positionSplitCoordinates (EuclideanSpace.single (2:Fin 3) 1) = (0,1) := by
    rw [← splitCoordinate_vertical_axis, ContinuousLinearEquiv.apply_symm_apply]
  unfold configurationRealLaplacian configurationRealPartial
  change (∑ a : Fin 1 × Fin 3, directionalSecond _ (EuclideanSpace.single a 1) x) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  simp_rw [hs]
  change positionSplitCoordinates (EuclideanSpace.single (Fin.last 2) 1) = (0,1) at hz
  rw [Fin.sum_univ_castSucc (n := 2),hz]
  simp_rw [hp]
  unfold splitLaplacian planarLaplacian
  simp_rw [split_planar_second f hf, split_vertical_second f hf]

end ContinuumCoulomb

end

end OAI
