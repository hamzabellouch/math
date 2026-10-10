import OAI.Geometry.NodalSets.Charts.CenteredSphereMetricLemmas
import OAI.Geometry.NodalSets.Charts.LocalMetricJets
import OAI.Geometry.NodalSets.Charts.RoundChartConnection
import OAI.Geometry.NodalSets.Elliptic.SeedLogConcreteJets

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section

def seedRealChart : BaseModel → ℝ := sphereSeedLogReal ∘ (extChartAt (𝓡 4) seedPoint).symm
def seedImagChart : BaseModel → ℝ := sphereSeedLogImag ∘ (extChartAt (𝓡 4) seedPoint).symm

lemma seed_chart_first (f : SeedAmbient → ℝ)
    (hf : DifferentiableAt ℝ f (seedPoint : SeedAmbient)) (v : BaseModel) :
    fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) seedPoint).symm) 0 v =
      fderiv ℝ f (seedPoint : SeedAmbient) (centeredSphereIsometry seedPoint v) := by
  let F : BaseModel → SeedAmbient := (Subtype.val : Base → SeedAmbient) ∘
    (extChartAt (𝓡 4) seedPoint).symm
  have hF0 : F 0 = (seedPoint : SeedAmbient) :=
    congrArg (Subtype.val : Base → SeedAmbient) (centeredSphereChart_inverse_zero seedPoint)
  have hd : HasFDerivAt F (centeredSphereIsometry seedPoint).toContinuousLinearMap 0 := by
    rw [show F = stereoInvFunAux (-(seedPoint : SeedAmbient)) ∘ centeredSphereIsometry seedPoint from
      centeredSphereChart_inverse seedPoint]
    have hh : HasFDerivAt (stereoInvFunAux (-(seedPoint : SeedAmbient)))
        (ContinuousLinearMap.id ℝ SeedAmbient) ((centeredSphereIsometry seedPoint).toContinuousLinearMap 0) := by
      simpa using hasFDerivAt_stereoInvFunAux (-(seedPoint : SeedAmbient))
    simpa using hh.comp (0:BaseModel) (centeredSphereIsometry seedPoint).toContinuousLinearMap.hasFDerivAt
  have hh := congrArg (fun L : BaseModel →L[ℝ] ℝ ↦ L v)
    ((hF0.symm ▸ hf).hasFDerivAt.comp 0 hd).fderiv
  change fderiv ℝ (f ∘ F) 0 v = fderiv ℝ f (F 0) (centeredSphereIsometry seedPoint v) at hh
  rw [hF0] at hh
  exact hh

lemma seed_round_hessian (u v : BaseModel) :
    localMetricHessian (roundChartMetric seedPoint) seedRealChart 0 u v =
      fderiv ℝ (fderiv ℝ seedLogReal) (seedPoint : SeedAmbient)
        (centeredSphereIsometry seedPoint u) (centeredSphereIsometry seedPoint v) - 2*⟪u,v⟫ := by
  rw [localMetricHessian_of_connection_zero _ _ _ (roundChartMetric_connection_zero seedPoint)]
  have hf : ContDiffAt ℝ ∞ seedLogReal (seedPoint : SeedAmbient) :=
    Complex.reCLM.contDiff.contDiffAt.comp _ (seedLog_contDiffAt seedPoint_mem_logDomain)
  rw [show seedRealChart = (fun x : Base ↦ seedLogReal x) ∘
    (extChartAt (𝓡 4) seedPoint).symm from rfl,
    sphere_restriction_chart_second_local seedLogReal seedPoint hf,
    seedLogReal_first_at_point]
  norm_num [seedPoint,seedPointVector,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  ring

lemma seed_round_gradient (u : BaseModel)
    (hu : centeredSphereIsometry seedPoint u = seedRealGradient) :
    localMetricGradient (roundChartMetric seedPoint) seedRealChart 0 = u := by
  apply localMetricGradient_eq_of_pair
  · intro v hv
    rw [roundChartMetric_center]
    exact real_inner_self_pos.mpr hv
  · intro v
    rw [roundChartMetric_center]
    change ⟪u,v⟫ = _
    rw [← (centeredSphereIsometry seedPoint).inner_map_map u v,hu]
    exact (seedRealGradient_pair _ (centeredSphereIsometry_orthogonal seedPoint v)).trans
      (seed_chart_first seedLogReal (seedLogReal_hasFDerivAt seedPoint_mem_logDomain).differentiableAt v).symm

theorem seed_round_admissibility :
    let g := roundChartMetric seedPoint
    let p := localMetricGradient g seedRealChart 0
    let H := localMetricHessian g seedRealChart 0
    p ≠ 0 ∧ ∃ t : BaseModel, g 0 p t = 0 ∧ g 0 t t = 1 ∧
      H p p + (g 0 p p + 4)*H t t = 243/16 ∧
      0 < H p p + (g 0 p p + 4)*H t t := by
  obtain ⟨u,hu⟩ := centeredSphereIsometry_exists seedPoint seedRealGradient seedRealGradient_tangent
  obtain ⟨t,ht⟩ := centeredSphereIsometry_exists seedPoint seedImagTestVector seedImagTest_tangent
  dsimp only
  rw [seed_round_gradient u hu]
  have huu : ⟪u,u⟫ = (29/4:ℝ) := by
    rw [← (centeredSphereIsometry seedPoint).inner_map_map u u,hu]
    exact seedGradient_geometry.1
  have hut : ⟪u,t⟫ = (0:ℝ) := by
    rw [← (centeredSphereIsometry seedPoint).inner_map_map u t,hu,ht]
    exact seedGradient_geometry.2.2.2.1
  have htt : ⟪t,t⟫ = (1:ℝ) := by
    rw [← (centeredSphereIsometry seedPoint).inner_map_map t t,ht]
    exact seedGradient_geometry.2.2.2.2
  have hu0 : u ≠ 0 := by intro h; norm_num [h] at huu
  have hHuu : localMetricHessian (roundChartMetric seedPoint) seedRealChart 0 u u = -1017/16 := by
    rw [seed_round_hessian,hu,seedLogReal_second_at_point,huu]
    norm_num [seedRealGradient,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  have hHtt : localMetricHessian (roundChartMetric seedPoint) seedRealChart 0 t t = 7 := by
    rw [seed_round_hessian,ht,seedLogReal_second_at_point,htt]
    norm_num [seedImagTestVector,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  refine ⟨hu0,t,?_,?_,?_,?_⟩
  · rw [roundChartMetric_center]; exact hut
  · rw [roundChartMetric_center]; exact htt
  · rw [roundChartMetric_center,hHuu,hHtt]
    change -1017/16 + (⟪u,u⟫+4)*7 = (243/16:ℝ)
    rw [huu]; norm_num
  · rw [roundChartMetric_center,hHuu,hHtt]
    change (0:ℝ) < -1017/16 + (⟪u,u⟫+4)*7
    rw [huu]; norm_num

end
end Yau.Target

end OAI
