import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianCorrectedLower
import OAI.Geometry.TamingCompatibility.Functional.HermitianCutoffDualBounds

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open Set Filter
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma ddc_zero_off (J : AlmostComplexStructure X) {f : X → ℝ} {x : X}
    (hx : x ∉ tsupport f) : exteriorDerivative (complexDifferential J f) x = 0 := by
  apply exteriorDerivative_eq_zero_of_eventually
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
  apply complexDifferential_zero_of_eventually J
  filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hy] with z hz
  exact image_eq_zero_of_notMem_tsupport hz

omit [IsManifold Model ∞ X] in
lemma chartLift_tsupport_subset [T2Space X] (p : X) {f : Space → ℝ}
    (hc : HasCompactSupport f) {K : Set Space} (hf : tsupport f ⊆ K)
    (hK : K ⊆ (extChartAt Model p).target) :
    tsupport (scalarChartLift p f) ⊆ (extChartAt Model p).symm '' K :=
  (scalarChartLift_tsupport p hc (hf.trans hK)).trans (image_mono hf)
end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.GeometricChart
open ManifoldForms Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : Data J α ht p)

lemma rawPair_zero_of_zero {a : TwoForm X} {z : Space}
    (ha : a ((extChartAt Model p).symm z) = 0) : rawPair J α ht p D a z = 0 := by
  have hr (j : Fin 4) : rawScalar J α ht p D a j z = 0 := by
    change a ((extChartAt Model p).symm z) _ = 0
    rw [ha]
    rfl
  ext i
  fin_cases i <;> simp only [rawPair,EuclideanEnergy.pair,hr] <;> rfl

end TamingCompatibility.GeometricChart

namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
variable (p : X) (D : Data J α ht p)
  {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma logSource_zero_off {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) {K : Set Space}
    (hbK : Metric.closedBall b (2*R) ⊆ K) {x : X}
    (hx : x ∉ (extChartAt Model p).symm '' K) :
    (logSource A J α hs ht p D hφ hc hφD hR hsp b hball).val.val x = 0 := by
  apply anti_ddc_zero_off
  intro h
  exact hx (image_mono hbK ((chartLift_tsupport_subset p
    (HermitianRadial.translatedCutoffLog_compact _ hR s b)
    (HermitianRadial.translatedCutoffLog_support _ hR s b)
    (hball.trans D.domain_subset)) h))

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma sqrtSource_zero_off {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) {K : Set Space}
    (hbK : Metric.closedBall b (2*R) ⊆ K) {x : X}
    (hx : x ∉ (extChartAt Model p).symm '' K) :
    (sqrtSource A J α hs ht p D hφ hc hφD hR hsp b hball).val.val x = 0 := by
  apply anti_ddc_zero_off
  intro h
  exact hx (image_mono hbK ((chartLift_tsupport_subset p
    (HermitianRadial.translatedCutoffSqrt_compact _ hR s b)
    (HermitianRadial.translatedCutoffSqrt_support _ hR s b)
    (hball.trans D.domain_subset)) h))

variable (D' : ∀ p : A.centers, Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D' p).source)
  (q : A.centers) (τ : 𝓢(Space,ℝ))
  {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
  (hψD : tsupport ψ ⊆ (D' q).domain)
  (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D' q).domain)
  (hτ : ∀ z ∈ K, τ z * coordinateWeight A q z = 1)
  (hψone : ∀ z ∈ K, ψ z = 1)
  (R : ℝ) (hR : 0 < R) (K₀ : Set Space) (hK₀ : IsCompact K₀)
  (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K)

include hD hK hτ hψone hK₀ in
lemma logSource_dual_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R),
    ∀ b, ∀ hb : b ∈ K₀,
    ‖antiEnergyDualLM A J α hs ht
      (logSource A J α hs ht q.val (D' q) hψ hcψ hψD hR hsr.1 b
        ((hcenters b hb).trans hKD))‖ ≤ C := by
  let W := hermitianCenterExtension J q.val (D' q) hψ hcψ hψD
  exact geometric_cutoffLog_dual_bound A J α hs ht D' hD W (W.smooth ⊤)
    q τ hψ hcψ hψD K hK hKD hτ hψone R hR K₀ hK₀ hcenters

include hD hK hτ hψone hK₀ in
lemma sqrtSource_dual_uniform : ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R),
    ∀ b, ∀ hb : b ∈ K₀,
    ‖antiEnergyDualLM A J α hs ht
      (sqrtSource A J α hs ht q.val (D' q) hψ hcψ hψD hR hsr.1 b
        ((hcenters b hb).trans hKD))‖ ≤ C := by
  let W := hermitianCenterExtension J q.val (D' q) hψ hcψ hψD
  exact geometric_cutoffSqrt_dual_bound A J α hs ht D' hD W (W.smooth ⊤)
    q τ hψ hcψ hψD K hK hKD hτ hψone R hR K₀ hK₀ hcenters
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
