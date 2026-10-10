import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.SmoothCorrection
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialGeometricCoefficient
import OAI.Geometry.TamingCompatibility.Charts.RadialCutoffSupported

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.ManifoldForms
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

def smoothDdc (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) : smoothForms X 2 :=
  ⟨exteriorDerivative (complexDifferential J f), (ddc_smooth_closed J hf).1⟩

lemma smoothDdc_closed (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) : IsClosed (smoothDdc J hf).val :=
  (ddc_smooth_closed J hf).2
end TamingCompatibility.ManifoldForms

namespace TamingCompatibility.GeometricHilbert
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart ManifoldVolume
open Set Filter ComplexMatrix MeasureTheory EuclideanSobolevOperators RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap LineDeriv RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, Data J α ht p.val)

def correctedDdc (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) : smoothForms X 2 :=
  smoothDdc J hf - closedLiftOfInverse A J α hs ht H Gs
    (smoothAntiProjection A J α hs ht (smoothDdc J hf))

omit [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma correctedDdc_closed (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (hHc : ∀ a, IsClosed (H a).val.val)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    IsClosed (correctedDdc A J α hs ht H Gs hf).val := by
  apply (mem_closedForms_iff _).mp
  apply Submodule.sub_mem
  · exact (mem_closedForms_iff _).mpr (smoothDdc_closed J hf)
  · exact (mem_closedForms_iff _).mpr
      (closedLiftOfInverse_closed A J α hs ht H Gs hHc _)

omit [T2Space X] in
lemma correctedDdc_invariant (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (hweak : ∀ a v, ⟪weakDelta A J α hs ht (antiToEnergy A J α hs ht (Gs a)),
      weakDelta A J α hs ht v⟫ =
      ⟪smoothL2 A J α hs ht true (a-H a).val,energyInclusion A J α hs ht v⟫)
    {f : X → ℝ} (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    IsInvariant (correctedDdc A J α hs ht H Gs hf).val J := by
  apply invariant_of_anti_zero J
  have he : smoothAntiProjection A J α hs ht (closedLiftOfInverse A J α hs ht H Gs
      (smoothAntiProjection A J α hs ht (smoothDdc J hf))) =
      smoothAntiProjection A J α hs ht (smoothDdc J hf) := by
    apply Subtype.ext
    apply Subtype.ext
    exact closedLiftOfInverse_rightInverse A J α hs ht H Gs hweak _
  have hz : smoothAntiProjection A J α hs ht (correctedDdc A J α hs ht H Gs hf) = 0 := by
    rw [correctedDdc,map_sub,he,sub_self]
  exact congrArg (fun a : antiPre A J α hs ht => a.val.val) hz

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma smoothAnti_ddc_cutoffLog (p : A.centers)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hφone : ∀ z ∈ K, φ z = 1)
    {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hb : Metric.closedBall b (2*R) ⊆ K) :
    smoothAntiProjection A J α hs ht (smoothDdc J
      (scalarChartLift_smooth p.val (translatedCutoffLog_smooth R hsp b)
        (translatedCutoffLog_compact hR s b)
        (((translatedCutoffLog_support hR s b).trans hb).trans
          (hKD.trans (D p).domain_subset)))) =
      scalarTestLM A J α hs ht D p K hK hKD 0
        (logCutoffSourceSupported (radialSourceExtension J p.val (D p) hφ hc hφD 0)
          ((radialSourceExtension J p.val (D p) hφ hc hφD 0).smooth ⊤) hR hsp K b hb) +
      scalarTestLM A J α hs ht D p K hK hKD 1
        (logCutoffSourceSupported (radialSourceExtension J p.val (D p) hφ hc hφD 1)
          ((radialSourceExtension J p.val (D p) hφ hc hφD 1).smooth ⊤) hR hsp K b hb) := by
  apply Subtype.ext
  apply Subtype.ext
  have he := anti_ddc_eq_manifoldTest J p.val (D p) hφ hc hφD
    (translatedCutoffLog_smooth R hsp b) (translatedCutoffLog_compact hR s b)
    (((translatedCutoffLog_support hR s b).trans hb).trans hKD)
    (fun z hz => hφone z (hb (translatedCutoffLog_support hR s b hz)))
  change antiInvariantPart J (exteriorDerivative (complexDifferential J _)) = _
  rw [he]
  change manifoldTest J α ht p.val (D p) (_ + _) = _
  rw [manifoldTest_add]
  rfl

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma smoothAnti_ddc_cutoffSqrt (p : A.centers)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hφone : ∀ z ∈ K, φ z = 1)
    {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hb : Metric.closedBall b (2*R) ⊆ K) :
    smoothAntiProjection A J α hs ht (smoothDdc J
      (scalarChartLift_smooth p.val (translatedCutoffSqrt_smooth R hsp b)
        (translatedCutoffSqrt_compact hR s b)
        (((translatedCutoffSqrt_support hR s b).trans hb).trans
          (hKD.trans (D p).domain_subset)))) =
      scalarTestLM A J α hs ht D p K hK hKD 0
        (sqrtCutoffSourceSupported (radialSourceExtension J p.val (D p) hφ hc hφD 0)
          ((radialSourceExtension J p.val (D p) hφ hc hφD 0).smooth ⊤) hR hsp K b hb) +
      scalarTestLM A J α hs ht D p K hK hKD 1
        (sqrtCutoffSourceSupported (radialSourceExtension J p.val (D p) hφ hc hφD 1)
          ((radialSourceExtension J p.val (D p) hφ hc hφD 1).smooth ⊤) hR hsp K b hb) := by
  apply Subtype.ext
  apply Subtype.ext
  have he := anti_ddc_eq_manifoldTest J p.val (D p) hφ hc hφD
    (translatedCutoffSqrt_smooth R hsp b) (translatedCutoffSqrt_compact hR s b)
    (((translatedCutoffSqrt_support hR s b).trans hb).trans hKD)
    (fun z hz => hφone z (hb (translatedCutoffSqrt_support hR s b hz)))
  change antiInvariantPart J (exteriorDerivative (complexDifferential J _)) = _
  rw [he]
  change manifoldTest J α ht p.val (D p) (_ + _) = _
  rw [manifoldTest_add]
  rfl
end TamingCompatibility.GeometricHilbert

end
end

section

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

def nonharmonicCorrectionLM (Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
    (p : X) (y : Space) : antiPre A J α hs ht →ₗ[ℝ] MetricForms.Form Space 2 :=
  (smoothPullbackLM p y).comp ((d.comp (antiDelta A J α hs ht)).comp Gs)

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

theorem nonharmonic_geometric_cutoffLog_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (q : Space) (hq : q ∈ U) (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
        (smoothAntiProjection A J α hs ht (smoothDdc J
          (scalarChartLift_smooth p.val (translatedCutoffLog_smooth R hsr.1 b)
            (translatedCutoffLog_compact hR s b)
            (((translatedCutoffLog_support hR s b).trans (hcenters b hb)).trans
              (hKU.trans (hUD.trans (D p).domain_subset))))))‖ ≤ C/(s+dist b y) := by
  let V := fun j : Fin 2 => radialSourceExtension J p.val (D p) hφ hc hφD j
  obtain ⟨δ₀,hδ₀,C₀,hC₀,hzero⟩ := scalarCorrection_cutoffLog_estimate
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ K hK hKU q hq
      0 (V 0) ((V 0).smooth ⊤) R hR K₀ hK₀ hcenters
  obtain ⟨δ₁,hδ₁,C₁,hC₁,hone⟩ := scalarCorrection_cutoffLog_estimate
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ K hK hKU q hq
      1 (V 1) ((V 1).smooth ⊤) R hR K₀ hK₀ hcenters
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro y hy s hsr b hb
  have hy₀ : y ∈ Metric.ball q δ₀ :=
    (show dist y q < min δ₀ δ₁ from hy).trans_le (min_le_left _ _)
  have hy₁ : y ∈ Metric.ball q δ₁ :=
    (show dist y q < min δ₀ δ₁ from hy).trans_le (min_le_right _ _)
  rw [smoothAnti_ddc_cutoffLog A J α hs ht D p hφ hc hφD K hK (hKU.trans hUD)
    hφone hR hsr.1 b (hcenters b hb),map_add]
  apply (norm_add_le _ _).trans
  have h₀ := hzero y hy₀ s hsr b hb
  have h₁ := hone y hy₁ s hsr b hb
  exact (add_le_add h₀ h₁).trans_eq (by rw [add_div])

include hD hH hweak hB hdual in

theorem nonharmonic_geometric_cutoffSqrt_estimate
    (p : A.centers) (τ ρ : 𝓢(Space,ℝ)) (U : Set Space)
    (hU : IsOpen U) (hUD : U ⊆ (D p).domain)
    (hτ : ∀ z ∈ U, τ z * coordinateWeight A p z = 1)
    (hρ : ∀ z ∈ U, ρ z = chartDensity J α p.val z)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKU : K ⊆ U)
    (hφone : ∀ z ∈ K, φ z = 1)
    (q : Space) (hq : q ∈ U) (R : ℝ) (hR : 0 < R)
    (K₀ : Set Space) (hK₀ : IsCompact K₀)
    (hcenters : ∀ b ∈ K₀, Metric.closedBall b (2*R) ⊆ K) (hR1 : 2*R ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Metric.ball q δ, ∀ s, ∀ hsr : s ∈ Ioc (0:ℝ) (2*R), ∀ b, ∀ hb : b ∈ K₀,
      ‖nonharmonicCorrectionLM A J α hs ht Gs p.val y
        (smoothAntiProjection A J α hs ht (smoothDdc J
          (scalarChartLift_smooth p.val (translatedCutoffSqrt_smooth R hsr.1 b)
            (translatedCutoffSqrt_compact hR s b)
            (((translatedCutoffSqrt_support hR s b).trans (hcenters b hb)).trans
              (hKU.trans (hUD.trans (D p).domain_subset))))))‖ ≤ C*(1+|Real.log (s+dist b y)|) := by
  let V := fun j : Fin 2 => radialSourceExtension J p.val (D p) hφ hc hφD j
  obtain ⟨δ₀,hδ₀,C₀,hC₀,hzero⟩ := scalarCorrection_cutoffSqrt_estimate
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ K hK hKU q hq
      0 (V 0) ((V 0).smooth ⊤) R hR K₀ hK₀ hcenters hR1
  obtain ⟨δ₁,hδ₁,C₁,hC₁,hone⟩ := scalarCorrection_cutoffSqrt_estimate
    A J α hs ht D hD H Gs hH hweak B hB hdual p τ ρ U hU hUD hτ hρ K hK hKU q hq
      1 (V 1) ((V 1).smooth ⊤) R hR K₀ hK₀ hcenters hR1
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,C₀+C₁,add_nonneg hC₀ hC₁,?_⟩
  intro y hy s hsr b hb
  have hy₀ : y ∈ Metric.ball q δ₀ :=
    (show dist y q < min δ₀ δ₁ from hy).trans_le (min_le_left _ _)
  have hy₁ : y ∈ Metric.ball q δ₁ :=
    (show dist y q < min δ₀ δ₁ from hy).trans_le (min_le_right _ _)
  rw [smoothAnti_ddc_cutoffSqrt A J α hs ht D p hφ hc hφD K hK (hKU.trans hUD)
    hφone hR hsr.1 b (hcenters b hb),map_add]
  apply (norm_add_le _ _).trans
  have h₀ := hzero y hy₀ s hsr b hb
  have h₁ := hone y hy₁ s hsr b hb
  exact (add_le_add h₀ h₁).trans_eq (by ring)

end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
