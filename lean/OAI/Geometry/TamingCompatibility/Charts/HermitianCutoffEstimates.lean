import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.HermitianCutoffSupported
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianDistance

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

include hD hH hweak hB hdual in

theorem scalarCorrection_cutoffLog_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.logCutoffSourceSupported W V hV hR hsr.1 K b (hcenters b hb))‖ ≤ C/(s+dist b y) := by
  obtain ⟨δ₁,hδ₁,C₁,hC₁,hsource⟩ :=
    scalarCorrection_logSource_distance_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W (scaledCutoff R) V hW (scaledCutoff_smooth R) hV
      (2*R) (scaledCutoff_tsupport hR) K₀ hK₀ hcenters
  obtain ⟨δ₂,hδ₂,C₂,hC₂,herror⟩ :=
    scalarCorrection_logError_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W V hW hV R hR (2*R) K₀ hK₀ hcenters
  obtain ⟨M,hM,hKM⟩ := hK₀.isBounded.subset_ball_lt 0 q
  let δ := min (min δ₁ δ₂) 1
  refine ⟨δ,lt_min (lt_min hδ₁ hδ₂) (by norm_num),C₁+C₂*(2*R+M+1),by positivity,?_⟩
  intro y hy s hsr b hb
  have hy₁ : y ∈ Metric.ball q δ₁ := (show dist y q < δ from hy).trans_le
    ((min_le_left _ _).trans (min_le_left _ _))
  have hy₂ : y ∈ Metric.ball q δ₂ := (show dist y q < δ from hy).trans_le
    ((min_le_left _ _).trans (min_le_right _ _))
  have hdM : s+dist b y ≤ 2*R+M+1 := by
    have hbM : dist b q < M := hKM hb
    have hy1 : dist q y ≤ 1 := by simpa only [dist_comm] using
      (show dist y q < δ from hy).le.trans (min_le_right _ _)
    linarith [dist_triangle b q y,hsr.2]
  have hden : 0 < s+dist b y := add_pos_of_pos_of_nonneg hsr.1 dist_nonneg
  rw [HermitianRadial.logCutoffSourceSupported_eq W V hW,map_add]
  apply (norm_add_le _ _).trans
  apply (add_le_add (hsource y hy₁ s hsr b hb) (herror y hy₂ s ⟨hsr.1.le,hsr.2⟩ b hb)).trans
  apply (le_div_iff₀ hden).mpr
  calc
    _ = C₁+C₂*(s+dist b y) := by field_simp
    _ ≤ _ := add_le_add (le_refl C₁) (mul_le_mul_of_nonneg_left hdM hC₂)

include hD hH hweak hB hdual in

theorem scalarCorrection_cutoffSqrt_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (q : Space) (hq : q ∈ U) (j : Fin 2)
    (W : Space → Space →L[ℝ] Space) (V : Space → Space) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀) (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) (hR1 : 2*R ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖scalarCorrectionLM A J α hs ht D Gs p K hK (hKU.trans hUD) j y
        (HermitianRadial.sqrtCutoffSourceSupported W V hV hR hsr.1 K b (hcenters b hb))‖ ≤ C*(1+|Real.log (s+dist b y)|) := by
  obtain ⟨δ₁,hδ₁,C₁,hC₁,hsource⟩ :=
    scalarCorrection_sqrtSource_distance_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W (scaledCutoff R) V hW (scaledCutoff_smooth R) hV
      (2*R) (scaledCutoff_tsupport hR) K₀ hK₀ hcenters hR1
  obtain ⟨δ₂,hδ₂,C₂,hC₂,herror⟩ :=
    scalarCorrection_sqrtError_estimate A J α hs ht D hD H Gs hH hweak B hB hdual
      p τ ρ U hU hUD hτ hρ K hK hKU q hq j W V hW hV R hR (2*R) K₀ hK₀ hcenters
  let δ := min (min δ₁ δ₂) 1
  refine ⟨δ,lt_min (lt_min hδ₁ hδ₂) (by norm_num),C₁+C₂,by positivity,?_⟩
  intro y hy s hsr b hb
  have hy₁ : y ∈ Metric.ball q δ₁ := (show dist y q < δ from hy).trans_le
    ((min_le_left _ _).trans (min_le_left _ _))
  have hy₂ : y ∈ Metric.ball q δ₂ := (show dist y q < δ from hy).trans_le
    ((min_le_left _ _).trans (min_le_right _ _))
  rw [HermitianRadial.sqrtCutoffSourceSupported_eq W V hW,map_add]
  apply (norm_add_le _ _).trans
  apply (add_le_add (hsource y hy₁ s hsr b hb) (herror y hy₂ s ⟨hsr.1.le,hsr.2⟩ b hb)).trans
  nlinarith [mul_nonneg hC₂ (abs_nonneg (Real.log (s+dist b y)))]

end TamingCompatibility.GeometricHilbert.Hermitian

end

end OAI
