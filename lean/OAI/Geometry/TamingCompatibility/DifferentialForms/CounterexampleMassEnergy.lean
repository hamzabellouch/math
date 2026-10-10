import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCorrectionLimit
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSeparatingMass

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart GeometricNormalCharts Filter
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ConnectedSpace X] [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel unitT2

theorem exists_counterexample_mass_energy_data
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α)
    (ht : Tames α J) (hc : IsClosed α)
    (hn : ¬ ∃ η : TwoForm X, IsSymplectic η ∧ Compatible η J) :
    ∃ A : FiniteCharts X,
    ∃ D : ∀ p : A.centers, HodgeChart.Data J α ht p.val,
    ∃ hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source,
    ∃ μ : Measure (MetricUnit (hermitianMetric J α hs ht)),
    ∃ hμ : IsProbabilityMeasure μ, letI := hμ
    ∃ B : antiPre A J α hs ht →ₗ[ℝ] smoothForms X 2,
      (∀ f, IsClosed (B f).val) ∧
      (∀ f, antiInvariantPart J (B f).val = f.val.val) ∧
      hodgeCorrectionSource A J α hs ht B (hermitianMetric J α hs ht) μ ⟨α,hs⟩ = -1 ∧
      (∀ a : PreL2 A J α hs ht true,
        Tendsto (fun r : ℝ => ⟪hodgeCorrectionFamily A J α hs ht D hD B
          (hermitianMetric J α hs ht) μ r,smoothL2 A J α hs ht true a⟫)
          (𝓝[>] 0) (𝓝 (hodgeCorrectionSource A J α hs ht B (hermitianMetric J α hs ht) μ a))) ∧
      ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
        let Qr := hodgeCorrectionRegularize A J α hs ht D hD B (hermitianMetric J α hs ht) μ r hr
        hodgeCubeRepresents A J α hs ht r
          (hodgeCorrectionSource A J α hs ht B (hermitianMetric J α hs ht) μ) Qr ∧
        l2Star A J α hs ht Qr = Qr ∧
        ∀ S : HodgeSmoothingCover A J α hs ht D hD r hr,
          let Pr := S.regularize (hermitianMetric J α hs ht) μ
          ‖Pr‖^2 ≤ C/r^2 ∧ |⟪Pr,Qr⟫| ≤ K*‖Qr‖ ∧
          ⟪Pr,l2Star A J α hs ht Pr⟫+2*⟪Pr,Qr⟫+‖Qr‖^2 = 0 := by
  obtain ⟨A,hE,hD⟩ := finite_common_parametrix_partition J α hs ht
  let E := fun p : A.centers => parametrixData J α hs ht p.val
  let D := fun p : A.centers => HodgeChart.data J α hs ht p.val
  obtain ⟨μ,hμ,-,-,hann,-⟩ := exists_geometric_separating_current J α hs ht hn
  let := hμ
  obtain ⟨B,hBc,hBR,L,hL,hB⟩ := exists_convergent_closed_lift A J α hs ht D hD (hermitianMetric J α hs ht)
  obtain ⟨C,K,hC,hK,hbounds⟩ := separating_current_mass_and_cross A J α hs ht E hE D hD μ hann
  refine ⟨A,D,hD,μ,hμ,B,hBc,hBR,
    hodgeCorrectionSource_taming A J α hs ht B hBc hBR μ hann hc,(hB μ).2,
    C,K,hC,hK,fun r hr hr1 => ?_⟩
  have hrep := ((hB μ).1 r hr hr1).1
  refine ⟨hrep,
    hodgeCorrectionRegularize_star A J α hs ht D hD B (hermitianMetric J α hs ht) μ r hr hrep,
    fun S => ⟨(hbounds r hr hr1 S).1,?_,?_⟩⟩
  · apply (hbounds r hr hr1 S).2
    intro a
    rw [hrep,map_sub,hodgeCorrectionSource_anti,sub_self]
  · exact hodgeCorrected_energy_identity A J α hs ht D hD B hBc hBR
      (hermitianMetric J α hs ht) μ hann r hr S hrep

end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
