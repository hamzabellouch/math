import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianCorrectedLower
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianGeometricEstimates

namespace OAI


noncomputable section
open Set Filter Topology

theorem IsCompact.exists_uniform_monotone_bound {Y : Type*} [TopologicalSpace Y]
    {K : Set Y} (hK : IsCompact K) (P : Y → ℝ → Prop)
    (hmono : ∀ y a b, a ≤ b → P y a → P y b)
    (hlocal : ∀ q ∈ K, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 q, P y C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, P y C := by
  classical
  have hloc : ∀ q : K, ∃ C : ℝ, ∃ U : Set Y,
      0 ≤ C ∧ IsOpen U ∧ q.val ∈ U ∧ ∀ y ∈ U, P y C := by
    intro q
    obtain ⟨C,hC,hq⟩ := hlocal q.val q.property
    obtain ⟨U,hUP,hU,hqU⟩ := mem_nhds_iff.mp hq
    exact ⟨C,U,hC,hU,hqU,hUP⟩
  choose C U hC hU hqU hUP using hloc
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU (by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hqU ⟨y,hy⟩⟩)
  refine ⟨∑ q ∈ s, C q, Finset.sum_nonneg (fun q _ => hC q), ?_⟩
  intro y hy
  obtain ⟨q,hq,hyq⟩ := mem_iUnion₂.mp (hs hy)
  exact hmono y (C q) _ (Finset.single_le_sum (fun r _ => hC r) hq) (hUP q y hyq)

end


noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
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
variable (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K)

include hD hH hweak hB hdual hU hτ hρ hK hφone hK₀ in

theorem nonharmonic_logSource_compact (L : Set Space) (hL : IsCompact L) (hLU : L ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ L, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
        (logSource A J α hs ht p.val (D p) hφ hc hφD hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD)))‖ ≤ C/(s+dist b y) := by
  apply _root_.OAI.IsCompact.exists_uniform_monotone_bound hL
  · intro y a c hac ha s hsr b hb
    have hsp : 0 < s := hsr.1
    exact (ha s hsr b hb).trans (div_le_div_of_nonneg_right hac (by positivity))
  · intro q hq
    let W := hermitianCenterExtension J p.val (D p) hφ hc hφD
    obtain ⟨δ,hδ,C,hC,hest⟩ := nonharmonic_geometric_cutoffLog_estimate
      A J α hs ht D hD H Gs hH hweak B hB hdual W (W.smooth ⊤)
      p τ ρ U hU hUD hτ hρ hφ hc hφD K hK hKU hφone q (hLU hq)
      R hR K₀ hK₀ hcenters
    refine ⟨C,hC,?_⟩
    filter_upwards [Metric.ball_mem_nhds q hδ] with y hy
    intro s hsr b hb
    exact hest y hy s hsr b hb

include hD hH hweak hB hdual hU hτ hρ hK hφone hK₀ in

theorem nonharmonic_sqrtSource_compact (hR1 : 2*R ≤ 1)
    (L : Set Space) (hL : IsCompact L) (hLU : L ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ L, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
        (sqrtSource A J α hs ht p.val (D p) hφ hc hφD hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD)))‖ ≤ C*(1+|Real.log (s+dist b y)|) := by
  apply _root_.OAI.IsCompact.exists_uniform_monotone_bound hL
  · intro y a c hac ha s hsr b hb
    exact (ha s hsr b hb).trans (mul_le_mul_of_nonneg_right hac (by positivity))
  · intro q hq
    let W := hermitianCenterExtension J p.val (D p) hφ hc hφD
    obtain ⟨δ,hδ,C,hC,hest⟩ := nonharmonic_geometric_cutoffSqrt_estimate
      A J α hs ht D hD H Gs hH hweak B hB hdual W (W.smooth ⊤)
      p τ ρ U hU hUD hτ hρ hφ hc hφD K hK hKU hφone q (hLU hq)
      R hR K₀ hK₀ hcenters hR1
    refine ⟨C,hC,?_⟩
    filter_upwards [Metric.ball_mem_nhds q hδ] with y hy
    intro s hsr b hb
    exact hest y hy s hsr b hb
end TamingCompatibility.GeometricHilbert.Hermitian

end

end OAI
