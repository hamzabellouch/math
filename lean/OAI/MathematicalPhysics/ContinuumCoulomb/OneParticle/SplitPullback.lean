import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitFormIdentity
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedWellField

namespace OAI

/-! Exact kinetic-energy pullback between physical Euclidean space and
planar/transverse product coordinates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def splitPullback (f : Position → ℝ) (p : SplitPosition) : ℝ :=
  f (positionSplitCoordinates.symm p)

theorem splitPullback_contDiff {f : Position → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (splitPullback f) :=
  hf.comp positionSplitCoordinates.symm.contDiff

theorem splitPullback_compact {f : Position → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (splitPullback f) :=
  hc.comp_homeomorph positionSplitCoordinates.symm.toHomeomorph

theorem splitPullback_integral (f : Position → ℝ) :
    (∫ p, splitPullback f p) = ∫ x, f x := by
  rw [← positionSplitCoordinates_integral (splitPullback f)]
  simp only [splitPullback, ContinuousLinearEquiv.symm_apply_apply]

theorem splitCoordinate_planar_axis (a : Fin 2) :
    positionSplitCoordinates.symm (planarAxis a,0) =
      EuclideanSpace.single (Fin.castSucc a) (1:ℝ) := by
  apply positionSplitCoordinates.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> fin_cases a <;>
      simp [planarAxis, positionSplitCoordinates_fst_zero, positionSplitCoordinates_fst_one]
  · rw [positionSplitCoordinates_snd]
    fin_cases a <;> simp

theorem splitCoordinate_vertical_axis :
    positionSplitCoordinates.symm (0,1) = EuclideanSpace.single (2:Fin 3) (1:ℝ) := by
  apply positionSplitCoordinates.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [positionSplitCoordinates_fst_zero, positionSplitCoordinates_fst_one]
  · rw [positionSplitCoordinates_snd]
    simp

theorem splitPullback_planar_partial {f : Position → ℝ} (hf : ContDiff ℝ 1 f)
    (a : Fin 2) (p : SplitPosition) :
    splitPlanarPartial (splitPullback f) a p =
      fderiv ℝ f (positionSplitCoordinates.symm p) (EuclideanSpace.single (Fin.castSucc a) 1) := by
  have h := ((hf.differentiable (by norm_num)) (positionSplitCoordinates.symm p)).hasFDerivAt.comp p
    positionSplitCoordinates.symm.hasFDerivAt
  have he := congrArg (fun L => L (planarAxis a,0)) h.fderiv
  unfold splitPlanarPartial splitPullback
  simpa only [Function.comp_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    splitCoordinate_planar_axis] using he

theorem splitPullback_vertical_partial {f : Position → ℝ} (hf : ContDiff ℝ 1 f)
    (p : SplitPosition) :
    splitVerticalPartial (splitPullback f) p =
      fderiv ℝ f (positionSplitCoordinates.symm p) (EuclideanSpace.single (2:Fin 3) 1) := by
  have h := ((hf.differentiable (by norm_num)) (positionSplitCoordinates.symm p)).hasFDerivAt.comp p
    positionSplitCoordinates.symm.hasFDerivAt
  have he := congrArg (fun L => L ((0:PlanarPosition),(1:ℝ))) h.fderiv
  unfold splitVerticalPartial splitPullback
  simpa only [Function.comp_def,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    splitCoordinate_vertical_axis] using he

def positionRealKinetic (f : Position → ℝ) : ℝ :=
  (1/2:ℝ)*∑ a : Fin 3, ∫ x, (fderiv ℝ f x (EuclideanSpace.single a 1))^2

def positionRealForm (V f : Position → ℝ) : ℝ :=
  positionRealKinetic f+∫ x, V x*f x^2

theorem splitPullback_kinetic {f : Position → ℝ} (hf : ContDiff ℝ 1 f) :
    splitRealKinetic (splitPullback f) = positionRealKinetic f := by
  unfold splitRealKinetic positionRealKinetic
  simp_rw [splitPullback_planar_partial hf, splitPullback_vertical_partial hf]
  have hi (a : Fin 3) : (∫ p, (fderiv ℝ f (positionSplitCoordinates.symm p)
      (EuclideanSpace.single a 1))^2) = ∫ x, (fderiv ℝ f x (EuclideanSpace.single a 1))^2 :=
    splitPullback_integral (fun x => (fderiv ℝ f x (EuclideanSpace.single a 1))^2)
  simp_rw [hi]
  rw [Fin.sum_univ_castSucc (n := 2)]
  rfl

theorem splitPullback_form (V : Position → ℝ) {f : Position → ℝ} (hf : ContDiff ℝ 1 f) :
    splitRealForm (fun p => V (positionSplitCoordinates.symm p)) (splitPullback f) =
      positionRealForm V f := by
  unfold splitRealForm positionRealForm
  rw [splitPullback_kinetic hf]
  congr 1
  exact splitPullback_integral (fun x => V x*f x^2)

end ContinuumCoulomb

end

end OAI
