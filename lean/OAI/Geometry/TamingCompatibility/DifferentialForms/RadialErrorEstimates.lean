import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialFixedJet
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialErrorSources

namespace OAI


noncomputable section
namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).source)
variable (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (hH : ∀ f, smoothL2 A J α hs ht true (H f).val =
    (harmonicAnti A J α hs ht).starProjection (smoothL2 A J α hs ht true f.val))
  (hweak : ∀ f v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs f)),
    weakDelta A J α hs ht v⟫ =
    ⟪smoothL2 A J α hs ht true (f-H f).val,energyInclusion A J α hs ht v⟫)
  (B : ℝ) (hB : 0 < B)
  (hdual : ∀ (f : antiPre A J α hs ht) (M : ℝ), 0 ≤ M →
    (∀ v : antiEnergy A J α hs ht,
      |⟪smoothL2 A J α hs ht true f.val,energyInclusion A J α hs ht v⟫| ≤ M*‖v‖) →
    ‖antiToEnergy A J α hs ht (Gs f)‖ ≤ B*M)

include hD hH hweak hB hdual in

theorem scalarCorrection_logError_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (S : ℝ)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s ∈ Icc (0:ℝ) S, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (logErrorSupported V hV hR K s b (hcenters b hb))‖ ≤ C := by
  obtain ⟨Q,hQ,hKQ⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space)
  obtain ⟨δ,hδ,C,hC,hest⟩ :=
    scalarCorrection_fixed_jet A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU 0 Q hQ.le hKQ q hq
  obtain ⟨E,hE,hinput⟩ := logErrorSchwartz_uniform_inputs V hV hR ρ (ρ.smooth ⊤) hK₀ S 3
  refine ⟨δ,hδ,C*E,by positivity,?_⟩
  intro y hy s hsr b hb
  have hin := hinput s hsr b hb
  exact hest y hy (logErrorSupported V hV hR K s b (hcenters b hb)) j E hE hin.1 hin.2

include hD hH hweak hB hdual in

theorem scalarCorrection_sqrtError_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (V : Space → Space) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R) (S : ℝ)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s ∈ Icc (0:ℝ) S, ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (sqrtErrorSupported V hV hR K s b (hcenters b hb))‖ ≤ C := by
  obtain ⟨Q,hQ,hKQ⟩ := hK.isBounded.subset_ball_lt 0 (0 : Space)
  obtain ⟨δ,hδ,C,hC,hest⟩ :=
    scalarCorrection_fixed_jet A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU 0 Q hQ.le hKQ q hq
  obtain ⟨E,hE,hinput⟩ := sqrtErrorSchwartz_uniform_inputs V hV hR ρ (ρ.smooth ⊤) hK₀ S 3
  refine ⟨δ,hδ,C*E,by positivity,?_⟩
  intro y hy s hsr b hb
  have hin := hinput s hsr b hb
  exact hest y hy (sqrtErrorSupported V hV hR K s b (hcenters b hb)) j E hE hin.1 hin.2

end TamingCompatibility.GeometricHilbert

end

end OAI
