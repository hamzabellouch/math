import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.HermitianManifoldTrace

namespace OAI

section
section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldHodge ManifoldLocalization GeometricChart Set Filter
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (H Gs : antiPre A J α hs ht →ₗ[ℝ] antiPre A J α hs ht)
  (p : X) (D : Data J α ht p)
  {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

def logForm {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) : smoothForms X 2 :=
  correctedDdc A J α hs ht H Gs
    (scalarChartLift_smooth p
      (HermitianRadial.translatedCutoffLog_smooth
        (hermitianCenterExtension J p D hφ hc hφD) R hsp b)
      (HermitianRadial.translatedCutoffLog_compact _ hR s b)
      (((HermitianRadial.translatedCutoffLog_support _ hR s b).trans hball).trans D.domain_subset))

def sqrtForm {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) : smoothForms X 2 :=
  correctedDdc A J α hs ht H Gs
    (scalarChartLift_smooth p
      (HermitianRadial.translatedCutoffSqrt_smooth
        (hermitianCenterExtension J p D hφ hc hφD) R hsp b)
      (HermitianRadial.translatedCutoffSqrt_compact _ hR s b)
      (((HermitianRadial.translatedCutoffSqrt_support _ hR s b).trans hball).trans D.domain_subset))

lemma cutoff_one_near {R : ℝ} (hR : 0 < R) {b y : Space} (hy : ‖y-b‖ < R)
    (hφone : ∀ z ∈ Metric.closedBall b (2*R), φ z = 1) :
    φ b = 1 ∧ φ =ᶠ[𝓝 y] fun _ => 1 := by
  refine ⟨hφone b (Metric.mem_closedBall_self (by positivity)),?_⟩
  filter_upwards [Metric.isOpen_ball.mem_nhds
    (show y ∈ Metric.ball b (2*R) by rw [Metric.mem_ball,dist_eq_norm]; linarith)] with z hz
  exact hφone z (Metric.ball_subset_closedBall hz)

lemma logForm_trace_lower {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b y v : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) (hy : ‖y-b‖ < R)
    (hφone : ∀ z ∈ Metric.closedBall b (2*R), φ z = 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hcor : ‖nonharmonicCorrectionLM A J α hs ht Gs p y
      (smoothAntiProjection A J α hs ht (smoothDdc J
        (scalarChartLift_smooth p
          (HermitianRadial.translatedCutoffLog_smooth
            (hermitianCenterExtension J p D hφ hc hφD) R hsp b)
          (HermitianRadial.translatedCutoffLog_compact _ hR s b)
          (((HermitianRadial.translatedCutoffLog_support _ hR s b).trans hball).trans D.domain_subset))))‖
        ≤ C/(s+‖y-b‖)) :
    let W := hermitianCenterExtension J p D hφ hc hφD
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    2*s^2*(‖v‖^2+‖W b v‖^2)/(s^2+‖y-b‖^2+‖W b (y-b)‖^2)^2 -
      (((1+M)^2*16*L*M+C*M)/(s+‖y-b‖))*‖v‖^2 ≤
      ManifoldForms.pullback (logForm A J α hs ht H Gs p D hφ hc hφD hR hsp b hball).val
        (extChartAt Model p).symm y ![v,coordinateJ J p y v] := by
  dsimp only
  obtain ⟨hφb,hφy⟩ := cutoff_one_near hR hy hφone
  let W := hermitianCenterExtension J p D hφ hc hφD
  let M := SchwartzMap.seminorm ℝ 0 0 W
  have hyT : y ∈ (extChartAt Model p).target := D.domain_subset
    (hball (by rw [Metric.mem_closedBall,dist_eq_norm]; linarith))
  have hJ : ‖coordinateJ J p y‖ ≤ M := by
    rw [← hermitianCenterExtension_eq J p D hφ hc hφD hφy.self_of_nhds]
    exact W.norm_le_seminorm ℝ y
  have hlow := manifold_cutoffLog_trace_lower J p D hφ hc hφD hR hsp b y v hball hy hφb hφy
  rw [logForm,correctedDdc_pullback_complexLine A J α hs ht H Gs _ p hyT]
  have hline := form_complexLine_norm_le
    (nonharmonicCorrectionLM A J α hs ht Gs p y
      (smoothAntiProjection A J α hs ht (smoothDdc J
        (scalarChartLift_smooth p (HermitianRadial.translatedCutoffLog_smooth W R hsp b)
          (HermitianRadial.translatedCutoffLog_compact W hR s b)
          (((HermitianRadial.translatedCutoffLog_support W hR s b).trans hball).trans D.domain_subset)))))
    (coordinateJ J p y) v
  have hbound : (C/(s+‖y-b‖))*‖coordinateJ J p y‖*‖v‖^2 ≤
      (C/(s+‖y-b‖))*M*‖v‖^2 := by gcongr
  have hh := hline.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcor (norm_nonneg _)) (sq_nonneg _)).trans hbound)
  rw [Real.norm_eq_abs] at hh
  have hu := (abs_le.mp hh).2
  dsimp only at hlow
  convert sub_le_sub hlow hu using 1
  first | rfl | (dsimp only [M,W]; ring)

lemma sqrtForm_trace_lower {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b y v : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) (hy : ‖y-b‖ < R)
    (hφone : ∀ z ∈ Metric.closedBall b (2*R), φ z = 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hcor : ‖nonharmonicCorrectionLM A J α hs ht Gs p y
      (smoothAntiProjection A J α hs ht (smoothDdc J
        (scalarChartLift_smooth p
          (HermitianRadial.translatedCutoffSqrt_smooth
            (hermitianCenterExtension J p D hφ hc hφD) R hsp b)
          (HermitianRadial.translatedCutoffSqrt_compact _ hR s b)
          (((HermitianRadial.translatedCutoffSqrt_support _ hR s b).trans hball).trans D.domain_subset))))‖
        ≤ C*(1+|Real.log (s+‖y-b‖)|)) :
    let W := hermitianCenterExtension J p D hφ hc hφD
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    ‖v‖^2/((1+M)*(s+‖y-b‖)) -
      (((1+M)^2*10*L*M)+C*M*(1+|Real.log (s+‖y-b‖)|))*‖v‖^2 ≤
      ManifoldForms.pullback (sqrtForm A J α hs ht H Gs p D hφ hc hφD hR hsp b hball).val
        (extChartAt Model p).symm y ![v,coordinateJ J p y v] := by
  dsimp only
  obtain ⟨hφb,hφy⟩ := cutoff_one_near hR hy hφone
  let W := hermitianCenterExtension J p D hφ hc hφD
  let M := SchwartzMap.seminorm ℝ 0 0 W
  have hyT : y ∈ (extChartAt Model p).target := D.domain_subset
    (hball (by rw [Metric.mem_closedBall,dist_eq_norm]; linarith))
  have hJ : ‖coordinateJ J p y‖ ≤ M := by
    rw [← hermitianCenterExtension_eq J p D hφ hc hφD hφy.self_of_nhds]
    exact W.norm_le_seminorm ℝ y
  have hlow := manifold_cutoffSqrt_trace_lower J p D hφ hc hφD hR hsp b y v hball hy hφb hφy
  rw [sqrtForm,correctedDdc_pullback_complexLine A J α hs ht H Gs _ p hyT]
  have hline := form_complexLine_norm_le
    (nonharmonicCorrectionLM A J α hs ht Gs p y
      (smoothAntiProjection A J α hs ht (smoothDdc J
        (scalarChartLift_smooth p (HermitianRadial.translatedCutoffSqrt_smooth W R hsp b)
          (HermitianRadial.translatedCutoffSqrt_compact W hR s b)
          (((HermitianRadial.translatedCutoffSqrt_support W hR s b).trans hball).trans D.domain_subset)))))
    (coordinateJ J p y) v
  have hbound : (C*(1+|Real.log (s+‖y-b‖)|))*‖coordinateJ J p y‖*‖v‖^2 ≤
      (C*(1+|Real.log (s+‖y-b‖)|))*M*‖v‖^2 := by gcongr
  have hh := hline.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcor (norm_nonneg _)) (sq_nonneg _)).trans hbound)
  rw [Real.norm_eq_abs] at hh
  have hu := (abs_le.mp hh).2
  dsimp only at hlow
  convert sub_le_sub hlow hu using 1
  first | rfl | (dsimp only [M,W]; ring)
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.Hermitian
open ManifoldForms ManifoldLocalization GeometricChart Set
open scoped Manifold ContDiff SchwartzMap
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (p : X) (D : Data J α ht p)
  {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
  (hφD : tsupport φ ⊆ D.domain)

def logSource {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) : antiPre A J α hs ht :=
  smoothAntiProjection A J α hs ht (smoothDdc J
    (scalarChartLift_smooth p
      (HermitianRadial.translatedCutoffLog_smooth
        (hermitianCenterExtension J p D hφ hc hφD) R hsp b)
      (HermitianRadial.translatedCutoffLog_compact _ hR s b)
      (((HermitianRadial.translatedCutoffLog_support _ hR s b).trans hball).trans D.domain_subset)))

def sqrtSource {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain) : antiPre A J α hs ht :=
  smoothAntiProjection A J α hs ht (smoothDdc J
    (scalarChartLift_smooth p
      (HermitianRadial.translatedCutoffSqrt_smooth
        (hermitianCenterExtension J p D hφ hc hφD) R hsp b)
      (HermitianRadial.translatedCutoffSqrt_compact _ hR s b)
      (((HermitianRadial.translatedCutoffSqrt_support _ hR s b).trans hball).trans D.domain_subset)))
end TamingCompatibility.GeometricHilbert.Hermitian

end
end

end
end

end OAI
