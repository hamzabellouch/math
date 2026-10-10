import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ComplexFormSplit
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.H1FiniteProjection

namespace OAI

/-! Volume- and kinetic-energy-preserving identification of one-electron
configuration space with physical three-dimensional space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def oneElectronCoordinates : Configuration 1 ≃ₗᵢ[ℝ] Position :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.uniqueProd (Fin 3) (Fin 1))

theorem oneElectronCoordinates_apply (x : Configuration 1) :
    oneElectronCoordinates x = Coulomb.position x 0 := rfl

theorem oneElectronCoordinates_single (a : Fin 3) :
    oneElectronCoordinates (EuclideanSpace.single (0,a) (1:ℝ)) = EuclideanSpace.single a 1 := by
  exact LinearIsometryEquiv.piLpCongrLeft_single _ _ _

theorem oneElectronCoordinates_symm_single (a : Fin 3) :
    oneElectronCoordinates.symm (EuclideanSpace.single a (1:ℝ)) =
      EuclideanSpace.single (0,a) 1 := by
  apply oneElectronCoordinates.injective
  rw [LinearIsometryEquiv.apply_symm_apply,oneElectronCoordinates_single]

theorem oneElectronCoordinates_integral (f : Position → ℝ) :
    (∫ x : Configuration 1, f (oneElectronCoordinates x)) = ∫ y, f y :=
  oneElectronCoordinates.measurePreserving.integral_comp
    oneElectronCoordinates.toHomeomorph.measurableEmbedding f

theorem oneElectronCoordinates_integral_complex (f : Position → ℂ) :
    (∫ x : Configuration 1, f (oneElectronCoordinates x)) = ∫ y, f y :=
  oneElectronCoordinates.measurePreserving.integral_comp
    oneElectronCoordinates.toHomeomorph.measurableEmbedding f

def oneElectronPullback (f : Configuration 1 → ℂ) (y : Position) : ℂ :=
  f (oneElectronCoordinates.symm y)

theorem oneElectronPullback_contDiff {f : Configuration 1 → ℂ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (oneElectronPullback f) := hf.comp oneElectronCoordinates.symm.contDiff

theorem oneElectronPullback_compact {f : Configuration 1 → ℂ} (hc : HasCompactSupport f) :
    HasCompactSupport (oneElectronPullback f) :=
  hc.comp_homeomorph oneElectronCoordinates.symm.toHomeomorph

theorem oneElectronPullback_partial {f : Configuration 1 → ℂ} (hf : ContDiff ℝ 1 f)
    (a : Fin 3) (y : Position) :
    fderiv ℝ (oneElectronPullback f) y (EuclideanSpace.single a 1) =
      fderiv ℝ f (oneElectronCoordinates.symm y) (EuclideanSpace.single (0,a) 1) := by
  have h := ((hf.differentiable (by norm_num)) (oneElectronCoordinates.symm y)).hasFDerivAt.comp y
    oneElectronCoordinates.symm.toContinuousLinearEquiv.hasFDerivAt
  have he := congrArg (fun L => L (EuclideanSpace.single a 1)) h.fderiv
  unfold oneElectronPullback
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,LinearIsometryEquiv.coe_coe,
    oneElectronCoordinates_symm_single] using he

theorem oneElectronPullback_integral (g : Configuration 1 → ℝ) :
    (∫ y, g (oneElectronCoordinates.symm y)) = ∫ x, g x := by
  rw [← oneElectronCoordinates_integral (fun y => g (oneElectronCoordinates.symm y))]
  simp only [LinearIsometryEquiv.symm_apply_apply]

theorem oneElectronPullback_integral_complex (g : Configuration 1 → ℂ) :
    (∫ y, g (oneElectronCoordinates.symm y)) = ∫ x, g x := by
  rw [← oneElectronCoordinates_integral_complex (fun y => g (oneElectronCoordinates.symm y))]
  simp only [LinearIsometryEquiv.symm_apply_apply]

theorem oneElectronPullback_form (V : Position → ℝ) {f : Configuration 1 → ℂ}
    (hf : ContDiff ℝ 1 f) :
    positionComplexForm V (oneElectronPullback f) =
      (1/2:ℝ)*(∑ a : Fin 3, ∫ x, ‖fderiv ℝ f x (EuclideanSpace.single (0,a) 1)‖^2)+
      ∫ x, V (oneElectronCoordinates x)*‖f x‖^2 := by
  unfold positionComplexForm positionComplexKinetic
  simp_rw [oneElectronPullback_partial hf]
  have hi (a : Fin 3) : (∫ y, ‖fderiv ℝ f (oneElectronCoordinates.symm y)
      (EuclideanSpace.single (0,a) 1)‖^2) =
      ∫ x, ‖fderiv ℝ f x (EuclideanSpace.single (0,a) 1)‖^2 :=
    oneElectronPullback_integral (fun x => ‖fderiv ℝ f x (EuclideanSpace.single (0,a) 1)‖^2)
  simp_rw [hi]
  congr 1
  have h := oneElectronPullback_integral
    (fun x => V (oneElectronCoordinates x)*‖f x‖^2)
  simpa only [oneElectronPullback,LinearIsometryEquiv.apply_symm_apply] using h

end ContinuumCoulomb

end

end OAI
