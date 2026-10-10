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
local instance hodgeCompactCutoffMetricTensorNormedAddCommGroup : NormedAddCommGroup (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedAddCommGroup
local instance hodgeCompactCutoffMetricTensorNormedSpace : NormedSpace ℝ (MetricTensor (V := Space)) := ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)

attribute [local irreducible] pulledA pulledB normalFirst normalZero normalDensity
  normalPrincipal normalGauge gaugedFirst gaugedZero

lemma compact_actual_cutoff (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    (O : Set Space) (hO : IsOpen O) (hOD : O ⊆ D.domain)
    (hgact : ∀ y ∈ O, g y = (coordinateMetric J α ht p y).bilinear)
    (hBact : ∀ y ∈ O, B y = frameMap (fun i => D.frame i y))
    (hsym : ∀ y v w, g y v w = g y w v)
    (K : Set Space) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ r : ℝ, 0 < r ∧
      K ×ˢ Metric.closedBall (0 : Space) r ⊆ gaugedDomain J α ht p D g B ∧
      ∀ χ : Space → ℝ, ContDiff ℝ ∞ χ → χ =ᶠ[𝓝 (0 : Space)] 1 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K, ∀ t : ℝ, 0 < t →
          ∀ z : Space, ‖z‖ ≤ r → ∀ u : W,
            ‖deriv (fun s => normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection s u z)) t +
              weightedAdjoint EuclideanEnergy.e (pulledA J α ht p D g B q)
                (pulledB J α ht p D g B q) (fun y => normalDensity g B (q,y))
                (differential EuclideanEnergy.e (pulledA J α ht p D g B q)
                  (pulledB J α ht p D g B q)
                  (fun y => normalGauge J α ht p D g B (q,y) (χ y • NormalHeatResidual.modelSection t u y))) z‖ ≤
              (C*FlatHeat.heat (2*t) z)*‖u‖ := by
  have hactual (q : Space) (hq : q ∈ K) : ActualData J α ht p D q g B :=
    ⟨O,hO,hKO hq,hOD,hgact,hBact,hsym⟩
  let Ω := gaugedDomain J α ht p D g B ∩ (fun x : Space × Space => normalMap g B x.1 x.2) ⁻¹' O
  have hΩ : IsOpen Ω := (gaugedDomain_open J α ht p D g B hg hB).inter
    (hO.preimage (normalMap_joint g B hg hB).continuous)
  have hKΩ : K ×ˢ {(0 : Space)} ⊆ Ω := by
    rintro ⟨q,z⟩ ⟨hq,hz⟩
    have hz' : z = 0 := hz
    subst z
    exact ⟨(hactual q hq).center J α ht p D g B,by simpa using hKO hq⟩
  obtain ⟨r,hr,hsub⟩ := compact_tube K hK Ω hΩ hKΩ
  refine ⟨r,hr,fun x hx => (hsub hx).1,fun χ hχ hχ0 => ?_⟩
  have hp (q : Space) (hq : q ∈ K) := (hactual q hq).jets J α hs ht p D q g B hg hB
  obtain ⟨C,hC,hbound⟩ := CutoffFamilies.compact_cutoff_residual
    (normalPrincipal g B) (gaugedFirst J α ht p D g B) (gaugedZero J α ht p D g B)
    K hK hr.le
    (fun x hx => normalPrincipal_smooth g B hg hB (hsub hx).1.1.2)
    (fun x hx => gaugedFirst_smooth J α ht p D g B hs hg hB (hsub hx).1)
    (fun x hx => gaugedZero_smooth J α ht p D g B hs hg hB (hsub hx).1)
    (fun q hq i j => by
      simpa only [normalPrincipal, NormalHeatResidual.euclideanPrincipal] using ((hp q hq).2.2.2.2.2.1 i j).2.1)
    (fun q hq i j => by
      simpa only [normalPrincipal] using ((hp q hq).2.2.2.2.2.1 i j).2.2)
    (fun q hq j => gaugedFirst_center J α ht p D g B hs hg hB (hactual q hq) j) χ hχ hχ0
  refine ⟨C,hC,fun q hq t htpos z hz u => ?_⟩
  have hx := hsub (show (q,z) ∈ K ×ˢ Metric.closedBall 0 r from ⟨hq,by simpa using hz⟩)
  rw [actual_cutoff_square_norm J α ht p D g B hs hg hB hsym (hactual q hq) hx.1.1
    (hgact _ hx.2) χ hχ htpos u]
  have hee : (EuclideanSpace.basisFun (Fin 4) ℝ : Fin 4 → Space) = EuclideanEnergy.e := by
    funext i
    simp [EuclideanEnergy.e]
  simpa only [hee] using hbound q hq z hz t htpos u

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
