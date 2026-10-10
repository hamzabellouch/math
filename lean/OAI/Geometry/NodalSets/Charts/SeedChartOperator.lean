import OAI.Geometry.NodalSets.Charts.SeedChartPrincipal
import OAI.Geometry.NodalSets.Elliptic.FiniteLinearity
import OAI.Geometry.NodalSets.Elliptic.IntrinsicWeightedLift

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry Yau.Jets
open scoped ContDiff
noncomputable section

lemma seedCoordPartial_pullback (f : BaseModel → ℝ) (hf : Differentiable ℝ f)
    (i : Fin 4) (x : Coord) :
    coordPartial i (fun z ↦ (f (seedCoordEquiv z):ℂ)) x =
      (fderiv ℝ f (seedCoordEquiv x) (EuclideanSpace.basisFun (Fin 4) ℝ i):ℂ) := by
  have hh : DifferentiableAt ℝ (fun z ↦ f (seedCoordEquiv z)) x :=
    (hf _).comp x seedCoordEquiv.differentiableAt
  rw [coordPartial_ofReal_at (fun z ↦ f (seedCoordEquiv z)) x hh]
  change (fderiv ℝ (f ∘ seedCoordEquiv) x (Pi.single i 1):ℂ) = _
  rw [seedCoordEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,seedCoordEquiv_basis]

lemma intrinsicRoundFlux_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) (i : Fin 4) :
    ContDiff ℝ ∞ (intrinsicRoundFlux A f p i) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have hz : z ∈ (extChartAt (𝓡 4) p).target := by rw [centeredSphereChart_target]; trivial
  apply (roundChartDensity_smooth_at p hz).mul
  apply ContDiffAt.sum
  intro j _
  exact (intrinsicSphereChartTensor_smoothAt A hA hs hp p hz i j).mul
    ((smooth_inverse_chart_derivative f hf p hz).clm_apply contDiffAt_const)

lemma seedCoordWeight_pos (rho : Base → ℝ) (hr : ∀ p, 0 < rho p) (x : Coord) :
    0 < seedCoordWeight rho x := by
  apply mul_pos (hr _)
  exact roundChartDensity_pos seedPoint (by rw [centeredSphereChart_target]; trivial)

lemma seedCoordWeight_smooth (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) : ContDiff ℝ ∞ (seedCoordWeight rho) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hz : seedCoordEquiv x ∈ (extChartAt (𝓡 4) seedPoint).target := by
    rw [centeredSphereChart_target]; trivial
  exact ((smooth_inverse_chart_comp rho hr seedPoint hz).mul
    (roundChartDensity_smooth_at seedPoint hz)).comp x seedCoordEquiv.contDiff.contDiffAt

lemma intrinsicSeedCoordFlux (A : IntrinsicTensor)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ∀ x, 0 < rho x)
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (i : Fin 4) :
    sourceFlux (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho)
      (fun x ↦ (f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)):ℂ)) i =
      fun x ↦ (intrinsicRoundFlux A f seedPoint i (seedCoordEquiv x):ℂ) := by
  have hf' : Differentiable ℝ (f ∘ (extChartAt (𝓡 4) seedPoint).symm) := fun z ↦
    (smooth_inverse_chart_comp f hf seedPoint
      (by rw [centeredSphereChart_target]; trivial)).differentiableAt (by simp)
  have hd (j : Fin 4) (x : Coord) :
      coordPartial j (fun z ↦ (f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv z)):ℂ)) x =
      (fderiv ℝ (f ∘ (extChartAt (𝓡 4) seedPoint).symm) (seedCoordEquiv x)
        (EuclideanSpace.basisFun (Fin 4) ℝ j):ℂ) :=
    seedCoordPartial_pullback (f ∘ (extChartAt (𝓡 4) seedPoint).symm) hf' j x
  funext x
  simp only [sourceFlux,intrinsicSeedCoordMetric_principal A hs hp rho hr,
    hd,intrinsicRoundFlux,seedCoordWeight,
    Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hne : (rho ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)):ℂ) ≠ 0 := by
    exact_mod_cast (hr ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x))).ne'
  field_simp

theorem intrinsicSeedCoordOperator (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ∀ x, 0 < rho x)
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (x : Coord) :
    sourceWeightedOperator (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho)
      (fun z ↦ (f ((extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv z)):ℂ)) x =
      (intrinsicWeightedChartOperator A rho f seedPoint (seedCoordEquiv x):ℂ) := by
  simp only [sourceWeightedOperator,complexDivergence,
    intrinsicSeedCoordFlux A hs hp rho hr f hf,
    seedCoordPartial_pullback _ ((intrinsicRoundFlux_smooth A hA hs hp f hf _ _).differentiable (by simp)),
    intrinsicWeightedChartOperator,seedCoordWeight,Complex.ofReal_mul,
    Complex.ofReal_inv,Complex.ofReal_sum,_root_.mul_inv_rev]
  ring

end
end Yau.Target

end OAI
