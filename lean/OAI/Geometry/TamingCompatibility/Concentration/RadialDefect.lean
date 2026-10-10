import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.HermitianCorrectedLower

namespace OAI

section

noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology RealInnerProductSpace SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def hermitianDefect (K : E →L[ℝ] E) (z v : E) : ℝ :=
  ‖hermitianGraph K z‖^2 * ‖hermitianGraph K v‖^2 -
    ⟪hermitianGraph K z,hermitianGraph K v⟫^2 -
    ⟪hermitianGraph K z,hermitianGraph K (K v)⟫^2

lemma hermitianDefect_nonneg (K : E →L[ℝ] E)
    (hK : ∀ v, K (K v) = -v) (z v : E) : 0 ≤ hermitianDefect K z v := by
  obtain ⟨ho,hn⟩ := hermitianGraph_complex_pair K hK v
  have h := two_direction_inner_sq_le (hermitianGraph K z)
    (hermitianGraph K v) (hermitianGraph K (K v)) ho hn
  dsimp only [hermitianDefect]
  linarith

lemma logPotential_trace_eq {s : ℝ} (hs : 0 < s) (z u v : E)
    (hv : ‖v‖ = ‖u‖) :
    fderiv ℝ (fderiv ℝ (logPotential s)) z u u +
      fderiv ℝ (fderiv ℝ (logPotential s)) z v v =
      2*(s^2*‖u‖^2 + (‖z‖^2*‖u‖^2 - ⟪z,u⟫^2 - ⟪z,v⟫^2)) /
        (s^2+‖z‖^2)^2 := by
  rw [logPotential_hessian hs,logPotential_hessian hs,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,hv]
  have h := ne_of_gt (radial_sq_pos hs z)
  field_simp
  ring

lemma hermitianLog_ddc_eq_defect (K : E →L[ℝ] E)
    (hK : ∀ v, K (K v) = -v) {s : ℝ} (hs : 0 < s) (z v : E) :
    extDeriv (ExteriorForms.dc (fun _ => K) (hermitianLogPotential K s)) z ![v,K v] =
      2*(s^2*‖hermitianGraph K v‖^2 + hermitianDefect K z v) /
        (s^2+‖hermitianGraph K z‖^2)^2 := by
  have hc := hermitianLogPotential_smooth K hs
  have hd : DifferentiableAt ℝ (fderiv ℝ (hermitianLogPotential K s)) z :=
    (hc.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  rw [constant_ddc_trace K hK hd]
  change fderiv ℝ (fderiv ℝ (fun x => logPotential s (hermitianGraph K x))) z v v +
    fderiv ℝ (fderiv ℝ (fun x => logPotential s (hermitianGraph K x))) z (K v) (K v) = _
  rw [linear_pullback_hessian _ (logPotential_smooth hs),
    linear_pullback_hessian _ (logPotential_smooth hs)]
  exact logPotential_trace_eq hs _ _ _ (hermitianGraph_complex_pair K hK v).2

lemma hermitianLog_variable_defect_lower {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {s : ℝ} (hs : 0 < s) (z v : E) (hJ : DifferentiableAt ℝ J z)
    (hJJ : ∀ v, J z (J z v) = -v) (hKK : ∀ v, K (K v) = -v)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hdiff : ‖J z-K‖ ≤ L*‖z‖) (hdJ : ‖fderiv ℝ J z‖ ≤ L)
    (hJn : ‖J z‖ ≤ M) (hKn : ‖K‖ ≤ M) :
    2*hermitianDefect K z v/(s^2+‖hermitianGraph K z‖^2)^2 -
      ((1+M)^2*(16*L*M/(s+‖z‖)))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc J (hermitianLogPotential K s)) z ![v,J z v] := by
  have hp := hermitianLog_ddc_perturbation K hs z v hJ hJJ hKK hL hM hdiff hdJ hJn hKn
  rw [hermitianLog_ddc_eq_defect K hKK hs,Real.norm_eq_abs,abs_le] at hp
  have hpos : 0 ≤ 2*(s^2*‖hermitianGraph K v‖^2)/(s^2+‖hermitianGraph K z‖^2)^2 := by positivity
  have he : 2*(s^2*‖hermitianGraph K v‖^2+hermitianDefect K z v) /
      (s^2+‖hermitianGraph K z‖^2)^2 =
      2*(s^2*‖hermitianGraph K v‖^2)/(s^2+‖hermitianGraph K z‖^2)^2 +
      2*hermitianDefect K z v/(s^2+‖hermitianGraph K z‖^2)^2 := by ring
  rw [he] at hp
  linarith [hp.1]

lemma schwartz_hermitianLog_defect_lower (W : 𝓢(E,E →L[ℝ] E)) {s : ℝ} (hs : 0 < s)
    (b y v : E) (hWy : ∀ w, W y (W y w) = -w) (hWb : ∀ w, W b (W b w) = -w) :
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    2*hermitianDefect (W b) (y-b) v/(s^2+‖hermitianGraph (W b) (y-b)‖^2)^2 -
      ((1+M)^2*(16*L*M/(s+‖y-b‖)))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc W (fun x => hermitianLogPotential (W b) s (x-b))) y ![v,W y v] := by
  dsimp only
  rw [ExteriorForms.extDeriv_dc_translate]
  have hJ : DifferentiableAt ℝ (fun z => W (b+z)) (y-b) :=
    ((W.smooth ⊤).comp (contDiff_const.add contDiff_id)).differentiable (by simp) _
  have he : b+(y-b)=y := by abel
  have h := hermitianLog_variable_defect_lower (W b) hs (y-b) v hJ
    (by simpa only [he] using hWy) hWb
    (apply_nonneg _ _) (apply_nonneg _ _)
    (by simpa only [he] using GeometricChart.schwartz_difference_bound W y b)
    (by simpa only [fderiv_comp_add_left,he] using GeometricChart.schwartz_fderiv_bound W y)
    (by simpa only [he] using W.norm_le_seminorm ℝ y) (W.norm_le_seminorm ℝ b)
  simpa only [he] using h
end TamingCompatibility.RadialPotential

namespace TamingCompatibility.HermitianRadial
open TamingCompatibility.RadialPotential Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology SchwartzMap RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [HasContDiffBump E]
lemma cutoffLog_defect_lower (W : 𝓢(E,E →L[ℝ] E)) {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (b y v : E) (hy : ‖y-b‖ < R)
    (hWy : ∀ w, W y (W y w) = -w) (hWb : ∀ w, W b (W b w) = -w) :
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    2*hermitianDefect (W b) (y-b) v/(s^2+‖hermitianGraph (W b) (y-b)‖^2)^2 -
      ((1+M)^2*(16*L*M/(s+‖y-b‖)))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc W (translatedCutoffLog W R s b)) y ![v,W y v] := by
  rw [ExteriorForms.extDeriv_dc_congr_germ Filter.EventuallyEq.rfl
    (translatedCutoffLog_germ W hR s b hy)]
  exact schwartz_hermitianLog_defect_lower W hs b y v hWy hWb
end TamingCompatibility.HermitianRadial

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricChart
open ManifoldForms ManifoldHodge Set Filter ContinuousAlternatingMap RadialPotential
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
 [T2Space X]
variable (J : AlmostComplexStructure X) (p : X)
variable {α : TwoForm X} {ht : Tames α J} (D : Data J α ht p)

lemma manifold_cutoffLog_defect_lower {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hφD : tsupport φ ⊆ D.domain)
    {R s : ℝ} (hR : 0 < R) (hs : 0 < s) (b y v : Space)
    (hball : Metric.closedBall b (2*R) ⊆ D.domain)
    (hy : ‖y-b‖ < R) (hφb : φ b = 1) (hφy : φ =ᶠ[𝓝 y] fun _ => 1) :
    let W := hermitianCenterExtension J p D hφ hc hφD
    let L := SchwartzMap.seminorm ℝ 0 1 W
    let M := SchwartzMap.seminorm ℝ 0 0 W
    2*hermitianDefect (W b) (y-b) v/(s^2+‖hermitianGraph (W b) (y-b)‖^2)^2 -
      ((1+M)^2*(16*L*M/(s+‖y-b‖)))*‖v‖^2 ≤
      ManifoldForms.pullback (exteriorDerivative (complexDifferential J (scalarChartLift p
        (HermitianRadial.translatedCutoffLog W R s b)))) (extChartAt Model p).symm y
          ![v,coordinateJ J p y v] := by
  dsimp only
  let W := hermitianCenterExtension J p D hφ hc hφD
  have hyD : y ∈ D.domain := hball (by rw [Metric.mem_closedBall,dist_eq_norm]; linarith)
  rw [pullback_ddc_scalarChartLift J p
    (HermitianRadial.translatedCutoffLog_smooth W R hs b)
    (HermitianRadial.translatedCutoffLog_compact W hR s b)
    (((HermitianRadial.translatedCutoffLog_support W hR s b).trans hball).trans D.domain_subset)
    (D.domain_subset hyD)]
  have hW := hermitianCenterExtension_eventually_eq J p D hφ hc hφD hφy
  rw [← ExteriorForms.extDeriv_dc_congr_germ hW Filter.EventuallyEq.rfl]
  rw [← hW.self_of_nhds]
  exact HermitianRadial.cutoffLog_defect_lower W hR hs b y v hy
    (hermitianCenterExtension_square J p D hφ hc hφD hφy.self_of_nhds)
    (hermitianCenterExtension_square J p D hφ hc hφD hφb)

end TamingCompatibility.GeometricChart

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

lemma logForm_defect_lower {R s : ℝ} (hR : 0 < R) (hsp : 0 < s) (b y v : Space)
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
    2*RadialPotential.hermitianDefect (W b) (y-b) v/(s^2+‖RadialPotential.hermitianGraph (W b) (y-b)‖^2)^2 -
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
  have hlow := manifold_cutoffLog_defect_lower J p D hφ hc hφD hR hsp b y v hball hy hφb hφy
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
  convert sub_le_sub hlow hu using 1; first | rfl | (dsimp only [M,W]; ring)

end TamingCompatibility.GeometricHilbert.Hermitian

end
end
end

end OAI
