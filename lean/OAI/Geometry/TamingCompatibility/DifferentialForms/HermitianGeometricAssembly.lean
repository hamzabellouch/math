import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.HermitianCutoffSupported

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
variable (W : Space → Space →L[ℝ] Space)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in

lemma smoothAnti_ddc_cutoffLog (p : A.centers)
    {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφD : tsupport φ ⊆ (D p).domain)
    (K : Set Space) (hK : IsCompact K) (hKD : K ⊆ (D p).domain)
    (hφone : ∀ z ∈ K, φ z = 1)
    {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hb : Metric.closedBall b (2*R) ⊆ K) :
    smoothAntiProjection A J α hs ht (smoothDdc J
      (scalarChartLift_smooth p.val (HermitianRadial.translatedCutoffLog_smooth W R hsp b)
        (HermitianRadial.translatedCutoffLog_compact W hR s b)
        (((HermitianRadial.translatedCutoffLog_support W hR s b).trans hb).trans
          (hKD.trans (D p).domain_subset)))) =
      scalarTestLM A J α hs ht D p K hK hKD 0
        (HermitianRadial.logCutoffSourceSupported W (radialSourceExtension J p.val (D p) hφ hc hφD 0)
          ((radialSourceExtension J p.val (D p) hφ hc hφD 0).smooth ⊤) hR hsp K b hb) +
      scalarTestLM A J α hs ht D p K hK hKD 1
        (HermitianRadial.logCutoffSourceSupported W (radialSourceExtension J p.val (D p) hφ hc hφD 1)
          ((radialSourceExtension J p.val (D p) hφ hc hφD 1).smooth ⊤) hR hsp K b hb) := by
  apply Subtype.ext
  apply Subtype.ext
  have he := anti_ddc_eq_manifoldTest J p.val (D p) hφ hc hφD
    (HermitianRadial.translatedCutoffLog_smooth W R hsp b) (HermitianRadial.translatedCutoffLog_compact W hR s b)
    (((HermitianRadial.translatedCutoffLog_support W hR s b).trans hb).trans hKD)
    (fun z hz => hφone z (hb (HermitianRadial.translatedCutoffLog_support W hR s b hz)))
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
      (scalarChartLift_smooth p.val (HermitianRadial.translatedCutoffSqrt_smooth W R hsp b)
        (HermitianRadial.translatedCutoffSqrt_compact W hR s b)
        (((HermitianRadial.translatedCutoffSqrt_support W hR s b).trans hb).trans
          (hKD.trans (D p).domain_subset)))) =
      scalarTestLM A J α hs ht D p K hK hKD 0
        (HermitianRadial.sqrtCutoffSourceSupported W (radialSourceExtension J p.val (D p) hφ hc hφD 0)
          ((radialSourceExtension J p.val (D p) hφ hc hφD 0).smooth ⊤) hR hsp K b hb) +
      scalarTestLM A J α hs ht D p K hK hKD 1
        (HermitianRadial.sqrtCutoffSourceSupported W (radialSourceExtension J p.val (D p) hφ hc hφD 1)
          ((radialSourceExtension J p.val (D p) hφ hc hφD 1).smooth ⊤) hR hsp K b hb) := by
  apply Subtype.ext
  apply Subtype.ext
  have he := anti_ddc_eq_manifoldTest J p.val (D p) hφ hc hφD
    (HermitianRadial.translatedCutoffSqrt_smooth W R hsp b) (HermitianRadial.translatedCutoffSqrt_compact W hR s b)
    (((HermitianRadial.translatedCutoffSqrt_support W hR s b).trans hb).trans hKD)
    (fun z hz => hφone z (hb (HermitianRadial.translatedCutoffSqrt_support W hR s b hz)))
  change antiInvariantPart J (exteriorDerivative (complexDifferential J _)) = _
  rw [he]
  change manifoldTest J α ht p.val (D p) (_ + _) = _
  rw [manifoldTest_add]
  rfl
end TamingCompatibility.GeometricHilbert.Hermitian

end

end OAI
