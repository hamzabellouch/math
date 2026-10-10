import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.GeometricQuadraticMass
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCorrectionLimit

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart Filter
open Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] unitMeasurable unitBorel unitT2

theorem exists_counterexample_energy_data [Nonempty X]
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
      hodgeCorrectionSource A J α hs ht B (hermitianMetric J α hs ht) μ ≠ 0 ∧
      hodgeCorrectionSource A J α hs ht B (hermitianMetric J α hs ht) μ ⟨α,hs⟩ = -1 ∧
      (∃ M : ℝ, 0 ≤ M ∧ ∀ x : X, ∀ s : ℝ, 0 < s →
        μ.real {u | hermitianEDist J α hs ht x u.val.proj < ENNReal.ofReal s} ≤ M*s^2) ∧
      (∀ a : PreL2 A J α hs ht true,
        Tendsto (fun r : ℝ => ⟪hodgeCorrectionFamily A J α hs ht D hD B
          (hermitianMetric J α hs ht) μ r,smoothL2 A J α hs ht true a⟫)
          (𝓝[>] 0) (𝓝 (hodgeCorrectionSource A J α hs ht B (hermitianMetric J α hs ht) μ a))) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (r : ℝ) (hr : 0 < r), r ≤ 1 →
        let Qr := hodgeCorrectionRegularize A J α hs ht D hD B (hermitianMetric J α hs ht) μ r hr
        hodgeCubeRepresents A J α hs ht r
          (hodgeCorrectionSource A J α hs ht B (hermitianMetric J α hs ht) μ) Qr ∧
        ‖Qr‖ ≤ K*(r⁻¹)^3 ∧
        l2Star A J α hs ht Qr = Qr ∧
        ∀ C : HodgeSmoothingCover A J α hs ht D hD r hr,
          let Pr := C.regularize (hermitianMetric J α hs ht) μ
          ⟪Pr,l2Star A J α hs ht Pr⟫+2*⟪Pr,Qr⟫+‖Qr‖^2 = 0 := by
  obtain ⟨A,hD⟩ := HodgeChart.finite_data_partition J α hs ht
  let D := fun p : A.centers => HodgeChart.data J α hs ht p.val
  obtain ⟨μ,hμ,-,-,hann,hpos⟩ := exists_geometric_separating_current J α hs ht hn
  let := hμ
  obtain ⟨B,hBc,hBR,K,hK,hB⟩ := exists_convergent_closed_lift A J α hs ht D hD (hermitianMetric J α hs ht)
  refine ⟨A,D,hD,μ,hμ,B,hBc,hBR,?_,
    hodgeCorrectionSource_taming A J α hs ht B hBc hBR μ hann hc,
    separating_probability_quadratic_growth J α hs ht μ hann,(hB μ).2,
    μ.real univ*K,mul_nonneg (measureReal_nonneg) hK,fun r hr hr1 => ?_⟩
  · intro hz
    have he := hodgeCorrectionSource_closed A J α hs ht B hBc hBR
      (hermitianMetric J α hs ht) μ hann ⟨α,hs⟩ hc
    have hp := hpos ⟨α,hs⟩ ht
    rw [hz] at he
    change (unitMeasureCurrent J (hermitianMetric J α hs ht) μ) ⟨α,hs⟩ + (0:ℝ) = 0 at he
    linarith
  · have hrep := ((hB μ).1 r hr hr1).1
    exact ⟨hrep,((hB μ).1 r hr hr1).2,
      hodgeCorrectionRegularize_star A J α hs ht D hD B (hermitianMetric J α hs ht) μ r hr hrep,
      fun C => hodgeCorrected_energy_identity A J α hs ht D hD B hBc hBR
        (hermitianMetric J α hs ht) μ hann r hr C hrep⟩
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
