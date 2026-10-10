import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCutoffBounds

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge NormalJets NormalMetricCalculus CoordinateOperator
open HodgeNormalSymbol FirstJetGauge OrthogonalJets Filter Set OperatorCalculus UniformJets
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
local instance parametrixResidualMetricTensorNormedAddCommGroup :
    NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance parametrixResidualMetricTensorNormedSpace :
    NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalPrincipal normalGauge gaugedFirst gaugedZero

lemma actual_cutoff_square_eq (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (hsym : ∀ y v w, g y v w = g y w v) {q z : Space}
    (hactual : ActualData J α ht p D q g B)
    (hz : (q,z) ∈ normalDomain J α ht p D g B)
    (hgact : g (normalMap g B q z) = (coordinateMetric J α ht p (normalMap g B q z)).bilinear)
    (χ : Space → ℝ) (hχ : ContDiff ℝ ∞ χ) {t : ℝ} (htpos : 0 < t) (u : W) :
      deriv (fun s => normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)) t +
        weightedAdjoint EuclideanEnergy.e (pulledA J α ht p D g B q)
          (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
          (differential EuclideanEnergy.e (pulledA J α ht p D g B q)
            (pulledB J α ht p D g B q)
            (fun y => normalGauge J α ht p D g B (q,y) (χ y • NormalHeatResidual.modelSection t u y))) z =
      normalGauge J α ht p D g B (q,z)
        (NormalHeatResidual.residual
          (fun y => CutoffFamilies.principal (normalPrincipal g B) χ (q,y))
          (fun y => CutoffFamilies.first (normalPrincipal g B) (gaugedFirst J α ht p D g B) χ (q,y))
          (fun y => CutoffFamilies.zero (normalPrincipal g B) (gaugedFirst J α ht p D g B)
            (gaugedZero J α ht p D g B) χ (q,y)) t z u) := by
  have hpa := pulledA_joint J α ht p D g B hg hB hz.1
  have hpb := pulledB_joint J α hs ht p D g B hg hB hz.1
  have hpρ := normalDensity_smooth g B hg hB hz.2
  have hU : ContDiff ℝ ∞ (fun y => normalGauge J α ht p D g B (q,y)) := by
    unfold normalGauge
    exact OrthogonalJets.gauge_contDiff (V := Space) (W := W)
      (halfJet (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4))
        (fun j => normalFirst J α ht p D g B j (q,0)))
  have hu : ∀ y, normalGauge J α ht p D g B (q,y) ∈ unitary (W →L[ℝ] W) :=
    normalGauge_unitary J α ht p D g B hs hg hB hactual
  have horth (y : Space) : (normalGauge J α ht p D g B (q,y)).adjoint ∘L
      normalGauge J α ht p D g B (q,y) = ContinuousLinearMap.id ℝ W := by
    simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.mul_def,ContinuousLinearMap.one_def]
      using (Unitary.star_mul_self_of_mem (hu y))
  have hρpos : normalDensity g B (q,z) ≠ 0 := by
    unfold normalDensity
    exact ne_of_gt (volumeDensity_pos hz.2)
  have hres := NormalHeatResidual.actual_cutoff_residual (pulledA J α ht p D g B q)
    (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
    (fun i j y => normalPrincipal g B i j (q,y))
    (fun y => normalGauge J α ht p D g B (q,y)) hU horth χ hχ
    (fun i => ((hpa i).comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    ((hpb.comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    ((hpρ.comp z (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
    hρpos (pulledA_scalar_at J α ht p D g B hg hB hsym hz.1 hgact) htpos u
  have hee : (EuclideanSpace.basisFun (Fin 4) ℝ : Fin 4 → Space) = EuclideanEnergy.e := by
    funext i
    simp [EuclideanEnergy.e]
  rw [hee] at hres
  have hf : gaugeFirst EuclideanEnergy.e (fun i j y => normalPrincipal g B i j (q,y))
      (firstMatrix EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y)))
      (fun y => normalGauge J α ht p D g B (q,y)) =
        (fun j y => gaugedFirst J α ht p D g B j (q,y)) := by
    unfold gaugedFirst normalFirst
    rfl
  have hc : gaugeZero EuclideanEnergy.e (fun i j y => normalPrincipal g B i j (q,y))
      (firstMatrix EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y)))
      (zeroMatrix EuclideanEnergy.e (pulledA J α ht p D g B q)
        (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y)))
      (fun y => normalGauge J α ht p D g B (q,y)) =
        (fun y => gaugedZero J α ht p D g B (q,y)) := by
    unfold gaugedZero normalFirst normalZero
    rfl
  rw [hf,hc] at hres
  have hcut := NormalHeatResidual.cutoff_gaussian_residual
    (fun i j y => normalPrincipal g B i j (q,y))
    (fun j y => gaugedFirst J α ht p D g B j (q,y))
    (fun y => gaugedZero J α ht p D g B (q,y)) χ hχ htpos z u
  rw [hee] at hcut
  rw [hcut] at hres
  have hcancel (v : W) : normalGauge J α ht p D g B (q,z)
      ((normalGauge J α ht p D g B (q,z)).adjoint v) = v := by
    exact congrArg (fun C : W →L[ℝ] W => C v) (by
      simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.mul_def,
        ContinuousLinearMap.one_def] using Unitary.mul_star_self_of_mem (hu z))
  have hh := congrArg (normalGauge J α ht p D g B (q,z)) hres
  rw [hcancel] at hh
  convert hh using 1
  simp only [NormalHeatResidual.residual,CutoffFamilies.principal,
    CutoffFamilies.first,CutoffFamilies.zero,hee]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
