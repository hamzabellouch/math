import OAI.Geometry.NodalSets.Charts.SeedChartScalarExtension
import OAI.Geometry.NodalSets.Coefficients.IntrinsicRealCorrection
import OAI.Geometry.NodalSets.Elliptic.IntrinsicRoundPerturbation

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets
open scoped ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

lemma seed_real_partial_pullback (f : Base → ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    fderiv ℝ (fun z ↦ f (seedSphereFromCoord z)) x (Pi.single i 1) =
      fderiv ℝ (f ∘ (extChartAt (𝓡 4) seedPoint).symm) (seedCoordEquiv x)
        (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  change fderiv ℝ ((f ∘ (extChartAt (𝓡 4) seedPoint).symm) ∘ seedCoordEquiv) x _ = _
  rw [seedCoordEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,seedCoordEquiv_basis]

lemma roundTensorPerturbation_seed_flux (a f : Base → ℝ) (x : Yau.Jets.Coord) (i : Fin 4) :
    intrinsicRoundFlux (roundTensorPerturbation a) f seedPoint i (seedCoordEquiv x) =
      roundCoordDensity x * (a (seedSphereFromCoord x) *
        roundCoordGradient (fun z ↦ f (seedSphereFromCoord z)) x i) := by
  rw [intrinsicRoundFlux,roundTensorPerturbation_chart,sphereRoundChartMatrix_inverse_conformal]
  have hfac : (((4:ℝ)/(‖seedCoordEquiv x‖^2+4))^2)⁻¹ = roundCoordFactor x := by
    unfold roundCoordFactor
    field_simp
  rw [hfac]
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,mul_ite,mul_one,mul_zero,
    ite_mul,zero_mul]
  rw [roundCoordGradient,seed_real_partial_pullback]
  simp [roundCoordDensity,seedSphereFromCoord,mul_assoc]

lemma roundTensorPerturbation_seed_divergence (a f : Base → ℝ) (x : Yau.Jets.Coord) :
    (roundCoordDensity x)⁻¹ *
      (∑ i, fderiv ℝ (intrinsicRoundFlux (roundTensorPerturbation a) f seedPoint i)
        (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i)) =
    Yau.weightedDiv roundCoordDensity (fun z i ↦ a (seedSphereFromCoord z) *
      roundCoordGradient (fun w ↦ f (seedSphereFromCoord w)) z i) x := by
  unfold Yau.weightedDiv Yau.coordDiv Yau.coordPartial
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun z ↦ roundCoordDensity z * (a (seedSphereFromCoord z) *
      roundCoordGradient (fun w ↦ f (seedSphereFromCoord w)) z i)) =
      (intrinsicRoundFlux (roundTensorPerturbation a) f seedPoint i) ∘ seedCoordEquiv := by
    funext z
    exact (roundTensorPerturbation_seed_flux a f z i).symm
  rw [he,seedCoordEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,seedCoordEquiv_basis]

end
end Yau.Target

end OAI
