import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianUnitMetric
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianCombinedForms

namespace OAI


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
lemma combinedForm_chart_lower (hR1 : 2*R ≤ 1) (a δ : ℝ) (ha : 0 ≤ a)
    (hδ : 0 < δ) (hδR : δ ≤ R)
    (hpos : ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ K, s+‖y-b‖ < δ → ∀ v : Space,
      0 ≤ ManifoldForms.pullback
        (combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v])
    (L : Set Space) (hL : IsCompact L) (hLU : L ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ∀ y ∈ L, ∀ v : Space, chartMetric J α p.val y v v = 1 →
      -C ≤ ManifoldForms.pullback
        (combinedForm A J α hs ht H Gs p.val (D p) hφ hc hφD a hR hsr.1 b
          ((hcenters b hb).trans (hKU.trans hUD))).val
        (extChartAt Model p.val).symm y ![v,coordinateJ J p.val y v] := by
  obtain ⟨C₀,hC₀,hlog⟩ := logForm_far_uniform
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters L hL hLU δ hδ
  obtain ⟨C₁,hC₁,hsqrt⟩ := sqrtForm_far_uniform
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ
    hφ hc hφD K hK hKU hφone R hR K₀ hK₀ hcenters hR1 L hL hLU δ hδ
  refine ⟨C₀+a*C₁,by positivity,?_⟩
  intro s hsr b hb y hy v hv
  by_cases hnear : s+‖y-b‖ < δ
  · have hyK : y ∈ K := hcenters b hb (by
      rw [Metric.mem_closedBall,dist_eq_norm]
      linarith [hsr.1])
    exact (neg_nonpos.mpr (by positivity) : -(C₀+a*C₁) ≤ 0).trans (hpos s hsr b hb y hyK hnear v)
  · have hl := hlog s hsr b hb y hy (le_of_not_gt hnear) v hv
    have hh := hsqrt s hsr b hb y hy (le_of_not_gt hnear) v hv
    have hl' := (neg_le_neg hl).trans (by simpa only [Real.norm_eq_abs] using neg_abs_le _)
    have hh' := mul_le_mul_of_nonneg_left ((neg_le_neg hh).trans (by simpa only [Real.norm_eq_abs] using neg_abs_le _)) ha
    calc
      -(C₀+a*C₁) = -C₀+a*(-C₁) := by ring
      _ ≤ _ := add_le_add hl' hh'
end TamingCompatibility.GeometricHilbert.Hermitian

end

end OAI
