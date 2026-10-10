import OAI.Geometry.NodalSets.Charts.SeedChartOperator
import OAI.Geometry.NodalSets.Charts.SphereDifferentialCoordinates
import OAI.Geometry.NodalSets.Coefficients.RoundSupportedCorrection
import OAI.Geometry.NodalSets.Elliptic.RealCoordinateEllipticLemmas

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

def intrinsicRealPrincipal (A : IntrinsicTensor) (p : Base) (x : Yau.Jets.Coord) :
    Matrix (Fin 4) (Fin 4) ℝ := intrinsicSphereChartTensor A p (seedCoordEquiv x)

def intrinsicRealDrift (A : IntrinsicTensor) (p : Base) (x : Yau.Jets.Coord) (j : Fin 4) : ℝ :=
  realEllipticDrift roundCoordDensity (intrinsicRealPrincipal A p) x j

def intrinsicRealPotential (rho : Base → ℝ) (lam : ℝ) (p : Base) (x : Yau.Jets.Coord) : ℝ :=
  lam*rho (sphereChartCoordMap p x)

lemma intrinsicRealPrincipal_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (p : Base) (i j : Fin 4) :
    ContDiff ℝ ∞ (fun x ↦ intrinsicRealPrincipal A p x i j) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact (intrinsicSphereChartTensor_smoothAt A hA hs hp p
    (by rw [centeredSphereChart_target]; trivial) i j).comp x seedCoordEquiv.contDiff.contDiffAt

lemma intrinsicRealPrincipal_symmetric (A : IntrinsicTensor)
    (hs : ∀ p v w, A p v w = A p w v) (p : Base) (x : Yau.Jets.Coord) (i j : Fin 4) :
    intrinsicRealPrincipal A p x i j = intrinsicRealPrincipal A p x j i :=
  hs _ _ _

lemma intrinsicRealPrincipal_posDef (A : IntrinsicTensor)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (p : Base) (x : Yau.Jets.Coord) : (intrinsicRealPrincipal A p x).PosDef :=
  intrinsicSphereChartTensor_posDef A hs hp p (by rw [centeredSphereChart_target]; trivial)

lemma intrinsicRealDrift_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (p : Base) (j : Fin 4) : ContDiff ℝ ∞ (fun x ↦ intrinsicRealDrift A p x j) :=
  realEllipticDrift_smooth roundCoordDensity roundCoordDensity_smooth
    (fun x ↦ (roundCoordDensity_pos x).ne') _ (intrinsicRealPrincipal_smooth A hA hs hp p) j

lemma intrinsicRealPotential_smooth (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (lam : ℝ) (p : Base) :
    ContDiff ℝ ∞ (intrinsicRealPotential rho lam p) :=
  contDiff_const.mul (spherePullback_smooth rho hr p)

lemma real_seedCoordPartial_pullback (f : BaseModel → ℝ) (i : Fin 4) (x : Yau.Jets.Coord) :
    Yau.coordPartial (f ∘ seedCoordEquiv) x i =
      fderiv ℝ f (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  unfold Yau.coordPartial
  rw [seedCoordEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,seedCoordEquiv_basis]

lemma intrinsicRealFlux_pullback (A : IntrinsicTensor) (w : Base → ℝ) (p : Base) (i : Fin 4) :
    intrinsicRoundFlux A w p i ∘ seedCoordEquiv =
      fun x ↦ roundCoordDensity x * ∑ j,
        intrinsicRealPrincipal A p x i j*Yau.coordPartial (w ∘ sphereChartCoordMap p) x j := by
  funext x
  have hd (j : Fin 4) := real_seedCoordPartial_pullback (w ∘ (extChartAt (𝓡 4) p).symm) j x
  change ∀ j, Yau.coordPartial (w ∘ sphereChartCoordMap p) x j = _ at hd
  simp only [Function.comp_apply,intrinsicRoundFlux,← hd,intrinsicRealPrincipal]
  rw [show roundChartDensity p (seedCoordEquiv x) = roundCoordDensity x by
    simp only [roundCoordDensity,roundChartDensity_conformal]]

theorem intrinsicRealOperator_pullback (A : IntrinsicTensor) (rho w : Base → ℝ)
    (p : Base) (x : Yau.Jets.Coord) :
    intrinsicWeightedChartOperator A rho w p (seedCoordEquiv x) =
      (rho (sphereChartCoordMap p x))⁻¹ * Yau.weightedDiv roundCoordDensity
        (fun y i ↦ ∑ j, intrinsicRealPrincipal A p y i j*
          Yau.coordPartial (w ∘ sphereChartCoordMap p) y j) x := by
  unfold intrinsicWeightedChartOperator Yau.weightedDiv Yau.coordDiv
  have hg : roundChartDensity p (seedCoordEquiv x) = roundCoordDensity x := by
    simp only [roundCoordDensity,roundChartDensity_conformal]
  rw [hg,mul_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_seedCoordPartial_pullback, intrinsicRealFlux_pullback]

theorem intrinsic_real_local_equation (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hrp : ∀ p, 0 < rho p)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z)) (p : Base) (x : Yau.Jets.Coord) :
    (∑ i, ∑ j, intrinsicRealPrincipal A p x i j*
      Yau.coordPartial (fun y ↦ Yau.coordPartial (w ∘ sphereChartCoordMap p) y j) x i) +
      (∑ j, intrinsicRealDrift A p x j*Yau.coordPartial (w ∘ sphereChartCoordMap p) x j) +
      intrinsicRealPotential rho lam p x*(w ∘ sphereChartCoordMap p) x = 0 := by
  have h := he p (seedCoordEquiv x)
  rw [intrinsicRealOperator_pullback, real_weighted_elliptic_expansion roundCoordDensity
    roundCoordDensity_smooth (fun y ↦ (roundCoordDensity_pos y).ne')
    (intrinsicRealPrincipal A p) (intrinsicRealPrincipal_smooth A hA hs hp p)
    (w ∘ sphereChartCoordMap p) (spherePullback_smooth w hw p)] at h
  change -((rho (sphereChartCoordMap p x))⁻¹ * _) = lam*w (sphereChartCoordMap p x) at h
  have hmul := congrArg (fun t : ℝ ↦ rho (sphereChartCoordMap p x)*t) h
  rw [mul_neg,← mul_assoc,mul_inv_cancel₀ (hrp _).ne',one_mul] at hmul
  dsimp [intrinsicRealDrift,intrinsicRealPotential,Function.comp_apply]
  linarith

end
end Yau.Target

end OAI
