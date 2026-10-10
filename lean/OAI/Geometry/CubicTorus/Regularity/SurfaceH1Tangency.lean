import Mathlib
import OAI.Geometry.CubicTorus.Estimates.SmoothScalarSeparatedTrunc
import OAI.Geometry.CubicTorus.Regularity.SurfaceGraphBundleMeasure

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_surfaceH1_chart_weak_gradient {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {U : Set Cover} (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) {R : ℝ}
    (hc : ∀ y ∈ Metric.closedBall (0 : Plane) R, ContinuousAt (fderiv ℝ g) y)
    (hgraph : ∀ᵐ x : Cover ∂volume, x ∈ U →
      (quotientMap x ∈ E ↔ ⟪n,x-a⟫ < graphHeightExtension a n g x))
    {φ : Cover → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsφ : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (hφO : tsupport φ ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    (hφR : tsupport φ ⊆ Metric.closedBall a R) (hφb : ∀ x, φ x ∈ Icc 0 1)
    {S : Set Plane} (hS : IsOpen S) (hgc : ContDiffOn ℝ 1 g S)
    (hunit : ∀ y ∈ S, φ (a+normalGraph n g y)=1)
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    ∃ (v : Lp ℝ 2 (volume.restrict S)) (G : Lp Plane 2 (volume.restrict S)),
      (v =ᵐ[volume.restrict S] fun y => u.1 (actualNormalGraphChart a hn g y)) ∧
      (G =ᵐ[volume.restrict S] fun y => graphCovector n g y
        (u.2 (actualNormalGraphChart a hn g y))) ∧
      PlaneWeakGradientOn S v G := by
  have hm := normalMeasure_graph_area_measure hE hμ a hn hg hc hgraph
    hφ hsφ hφU hφO hφR hφb
  have hd := graph_chart_measure_le a hn hg.continuous hφb hm hS.measurableSet hunit
  have hcS (y : Plane) (hy : y∈S) (i : Fin 3) : (a+normalGraph n g y) i∈Icc 0 1 := by
    have hsupport : a+normalGraph n g y∈tsupport φ := subset_tsupport _ (by
      rw [Function.mem_support,hunit y hy]
      exact one_ne_zero)
    exact ⟨(hφO hsupport i).1.le,(hφO hsupport i).2.le⟩
  let hchart := actualNormalGraphChart_measurable a hn hg.continuous
  let v := lpPullbackLE hchart hd u.1
  let w := lpPullbackLE hchart hd u.2
  let G := graphCovectorLp hn hg w
  refine ⟨v,G,lpPullbackLE_ae hchart hd u.1,?_,?_⟩
  · filter_upwards [graphCovectorLp_ae hn hg w,lpPullbackLE_ae hchart hd u.2] with y hyv hyw
    change G y=_ at hyv
    change w y = u.2 (actualNormalGraphChart a hn g y) at hyw
    simpa only [hyw] using hyv
  · exact surfaceH1_chart_weak_gradient μ a hn hg hS hgc hcS hd hu

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPairing_memLp (μ : FiniteMeasure NormalBundle) :
    MemLp (fun z : NormalBundle => innerSL ℝ (z.2 : Cover)) ∞ (μ : Measure NormalBundle) := by
  have hc : Continuous (fun z : NormalBundle => innerSL ℝ (z.2 : Cover)) :=
    (innerSL ℝ : Cover →L[ℝ] Cover →L[ℝ] ℝ).continuous.comp
      (continuous_subtype_val.comp continuous_snd)
  apply memLp_top_of_bound hc.aestronglyMeasurable 1
  filter_upwards [] with z
  rw [innerSL_apply_norm]
  exact (show ‖(z.2 : Cover)‖=1 from z.2.property).le

def surfaceNormalPairing (μ : FiniteMeasure NormalBundle) :
    Lp Cover 2 (μ : Measure NormalBundle) →L[ℝ] Lp ℝ 2 (μ : Measure NormalBundle) :=
  (ContinuousLinearMap.id ℝ (Cover →L[ℝ] ℝ)).holderL (μ : Measure NormalBundle) ∞ 2 2
    ((normalPairing_memLp μ).toLp (fun z : NormalBundle => innerSL ℝ (z.2 : Cover)))

lemma surfaceNormalPairing_ae (μ : FiniteMeasure NormalBundle)
    (u : Lp Cover 2 (μ : Measure NormalBundle)) :
    surfaceNormalPairing μ u =ᵐ[(μ : Measure NormalBundle)]
      fun z => ⟪(z.2 : Cover),u z⟫ := by
  have ha := (normalPairing_memLp μ).coeFn_toLp
  have hb := (ContinuousLinearMap.id ℝ (Cover →L[ℝ] ℝ)).coeFn_holder
    ((normalPairing_memLp μ).toLp (fun z : NormalBundle => innerSL ℝ (z.2 : Cover))) u (r := 2)
  filter_upwards [ha,hb] with z ha hb
  change (surfaceNormalPairing μ u) z=_ at hb
  simp only [ContinuousLinearMap.id_apply,ha] at hb
  exact hb

lemma smoothScalarGradient_tangent (f : smoothPeriodicScalars) (z : NormalBundle) :
    ⟪(z.2 : Cover),smoothScalarGradient f z⟫=0 := by
  change ⟪(z.2 : Cover),gradient f.val z.1-
    ⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover)⟫=0
  rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,z.2.property]
  ring

lemma surfaceSmoothJet_tangent (μ : FiniteMeasure NormalBundle) (f : smoothPeriodicScalars) :
    surfaceNormalPairing μ (surfaceSmoothJet μ f).2=0 := by
  apply Lp.ext
  filter_upwards [surfaceNormalPairing_ae μ (surfaceSmoothJet μ f).2,
    (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (μ : Measure NormalBundle))] with z hz hf hz0
  change (surfaceSmoothJet μ f).2 z=smoothScalarGradient f z at hf
  rw [hz,hf,smoothScalarGradient_tangent,hz0]
  rfl

theorem surfaceH1_tangent (μ : FiniteMeasure NormalBundle) {u : SurfaceJet μ}
    (hu : u∈surfaceH1 μ) :
    ∀ᵐ z ∂(μ : Measure NormalBundle),⟪(z.2 : Cover),u.2 z⟫=0 := by
  let F : SurfaceJet μ → Lp ℝ 2 (μ : Measure NormalBundle) := fun w => surfaceNormalPairing μ w.2
  have hF : Continuous F := (surfaceNormalPairing μ).continuous.comp continuous_snd
  have hrange : Set.range (surfaceSmoothJet μ) ⊆ {w | F w=0} := by
    rintro _ ⟨f,rfl⟩
    exact surfaceSmoothJet_tangent μ f
  have hclosed : IsClosed {w | F w=0} := isClosed_eq hF continuous_const
  have he : F u=0 := closure_minimal hrange hclosed hu
  have hz := Lp.coeFn_zero (E := ℝ) (p := 2) (μ := (μ : Measure NormalBundle))
  have hae := surfaceNormalPairing_ae μ u.2
  change surfaceNormalPairing μ u.2=0 at he
  rw [he] at hae
  exact hae.symm.trans hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphCovector_metric_pairing {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (y : Plane) (v w : Cover)
    (hw : ⟪graphSlopeNormal n (gradient g y),w⟫=0) :
    ⟪v,w⟫=cmcWeight (gradient g y)*
      ⟪graphCovector n g y v,cmcJacobian (gradient g y) (graphCovector n g y w)⟫ := by
  have hp := graph_metric_projection hn (gradient g y) w
  change normalPlaneEmbedding n (graphInverseMetric (gradient g y) (graphCovector n g y w))+
    ⟪gradient g y,graphInverseMetric (gradient g y) (graphCovector n g y w)⟫ • n = _ at hp
  rw [hw,zero_smul,sub_zero] at hp
  calc
    ⟪v,w⟫ = ⟪graphCovector n g y v,
        graphInverseMetric (gradient g y) (graphCovector n g y w)⟫ := by
      rw [graphCovector_duality hn,hp]
    _ = _ := by rw [graphInverseMetric,smul_apply,inner_smul_right]

lemma smoothScalarGradient_graph_pairing (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (f : smoothPeriodicScalars) {g : Plane → ℝ} {y : Plane}
    (hgy : DifferentiableAt ℝ g y)
    (hy : ∀ i,(a+normalGraph n g y) i∈Icc 0 1) (v : Cover) :
    ⟪v,smoothScalarGradient f (actualNormalGraphChart a hn g y)⟫=
      cmcWeight (gradient g y)*⟪graphCovector n g y v,
        cmcJacobian (gradient g y) (gradient (fun z => f.val (a+normalGraph n g z)) y)⟫ := by
  have ht := smoothScalarGradient_tangent f (actualNormalGraphChart a hn g y)
  rw [actualNormalGraphChart_normal] at ht
  rw [graphCovector_metric_pairing hn g y v _ ht,
    smoothScalarGradient_graph_covector a hn f hgy hy]

lemma graph_area_integral {μ : Measure NormalBundle} (a : Cover) {n : Cover}
    (hn : ‖n‖=1) {g : Plane → ℝ} (hg : Continuous g)
    {φ : Cover → ℝ} (hφ : Measurable φ) (hφ0 : ∀ x,0≤φ x)
    (hm : μ.withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    {F : NormalBundle → ℝ} (hF : AEStronglyMeasurable F μ) :
    (∫ z,φ z.1*F z ∂μ)=∫ y,φ (a+normalGraph n g y)*‖graphAreaVector n g y‖*
      F (actualNormalGraphChart a hn g y) := by
  have hf : Measurable (fun z : NormalBundle => ENNReal.ofReal (φ z.1)) :=
    (hφ.comp (measurable_subtype_coe.comp measurable_fst)).ennreal_ofReal
  have hG : Measurable (fun y => ENNReal.ofReal
      (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)) := by
    have hc : Continuous (fun y => a+normalGraph n g y) :=
      graph_trace_continuous a n hg continuous_id
    have hmgrad : Measurable (gradient g) :=
      (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
    have harea : Measurable (fun y => ‖graphAreaVector n g y‖) := by
      exact (measurable_const.sub ((normalPlaneLinearIsometry n).continuous.measurable.comp hmgrad)).norm
    exact ((hφ.comp hc.measurable).mul harea).ennreal_ofReal
  have hFm : AEStronglyMeasurable F (μ.withDensity (fun z => ENNReal.ofReal (φ z.1))) :=
    hF.mono_ac (withDensity_absolutelyContinuous _ _)
  have he := congrArg (fun ν : Measure NormalBundle => ∫ z,F z ∂ν) hm
  rw [integral_map (actualNormalGraphChart_measurable a hn hg).aemeasurable
    (by rwa [← hm])] at he
  rw [integral_withDensity_eq_integral_toReal_smul hf
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul hG
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))] at he
  simpa only [ENNReal.toReal_ofReal (hφ0 _),
    ENNReal.toReal_ofReal (mul_nonneg (hφ0 _) (norm_nonneg _)),smul_eq_mul] using he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def periodicGraphScalar (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) : smoothPeriodicScalars :=
  ⟨latticePeriodize (fun x => χ x*graphHeightExtension a n ψ x),
    latticePeriodize_contDiff (hχ.mul (graphHeightExtension_contDiff a n hψ)) hc.mul_right,
    latticePeriodize_periodic _⟩

lemma periodicGraphScalar_germ (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : CompactCell) :
    (periodicGraphScalar a n hχ hc hψ).val =ᶠ[𝓝 (x : Cover)]
      (fun z => χ z*graphHeightExtension a n ψ z) :=
  latticePeriodize_eventuallyEq hc.mul_right
    (tsupport_mul_subset_left.trans hO) (compactCell_coordinates x)

lemma periodicGraphScalar_zero_germ (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : CompactCell)
    (hx : (x : Cover)∉tsupport χ) :
    (periodicGraphScalar a n hχ hc hψ).val =ᶠ[𝓝 (x : Cover)] (fun _ => 0) := by
  apply (periodicGraphScalar_germ a n hχ hc hO hψ x).trans
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
  simp only [Pi.zero_apply] at hy
  simp only [hy,zero_mul]

lemma periodicGraphScalar_graph_germ (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {g : Plane → ℝ} (hg : Continuous g) {S : Set Plane} (hS : IsOpen S)
    (hunit : ∀ y ∈ S,χ (a+normalGraph n g y)=1) (hs : tsupport ψ⊆S)
    {y : Plane} (hy : ∀ i,(a+normalGraph n g y) i∈Icc 0 1) :
    (fun z => (periodicGraphScalar a n hχ hc hψ).val (a+normalGraph n g z))=ᶠ[𝓝 y] ψ := by
  have hpos := actualNormalGraphChart_position a hn g hy
  have he := periodicGraphScalar_germ a n hχ hc hO hψ (actualNormalGraphChart a hn g y).1
  rw [hpos] at he
  have htrace : Continuous (fun z => a+normalGraph n g z) :=
    graph_trace_continuous a n hg continuous_id
  apply (he.comp_tendsto htrace.continuousAt).trans
  have hval (z : Plane) : graphHeightExtension a n ψ (a+normalGraph n g z)=ψ z := by
    rw [graphHeightExtension,add_sub_cancel_left,normalPlaneCoordinates_graph hn]
  by_cases hys : y∈tsupport ψ
  · filter_upwards [hS.mem_nhds (hs hys)] with z hz
    dsimp only [Function.comp_apply]
    rw [hval,hunit z hz,one_mul]
  · filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hys] with z hz
    dsimp only [Function.comp_apply]
    simp only [Pi.zero_apply] at hz
    rw [hval,hz,mul_zero]

lemma periodicGraphScalar_graph_value (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {g : Plane → ℝ} (hg : Continuous g) {S : Set Plane} (hS : IsOpen S)
    (hunit : ∀ y ∈ S,χ (a+normalGraph n g y)=1) (hs : tsupport ψ⊆S)
    {y : Plane} (hy : ∀ i,(a+normalGraph n g y) i∈Icc 0 1) :
    smoothScalarValue (periodicGraphScalar a n hχ hc hψ) (actualNormalGraphChart a hn g y)=ψ y := by
  change (periodicGraphScalar a n hχ hc hψ).val (actualNormalGraphChart a hn g y).1=ψ y
  rw [actualNormalGraphChart_position a hn g hy]
  exact (periodicGraphScalar_graph_germ a hn hχ hc hO hψ hg hS hunit hs hy).eq_of_nhds

lemma periodicGraphScalar_graph_covector (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {g : Plane → ℝ} (hg : Continuous g) {S : Set Plane} (hS : IsOpen S)
    (hunit : ∀ y ∈ S,χ (a+normalGraph n g y)=1) (hs : tsupport ψ⊆S)
    {y : Plane} (hgy : DifferentiableAt ℝ g y)
    (hy : ∀ i,(a+normalGraph n g y) i∈Icc 0 1) :
    graphCovector n g y (smoothScalarGradient (periodicGraphScalar a n hχ hc hψ)
      (actualNormalGraphChart a hn g y))=gradient ψ y := by
  rw [smoothScalarGradient_graph_covector a hn _ hgy hy]
  have he := (periodicGraphScalar_graph_germ a hn hχ hc hO hψ hg hS hunit hs hy).fderiv_eq (𝕜 := ℝ)
  simp only [gradient,he]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceJacobiB_smooth_integral (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u : SurfaceJet μ)
    (f : smoothPeriodicScalars) :
    surfaceJacobiB μ q u (surfaceSmoothJet μ f)=
      ∫ z,⟪u.2 z,smoothScalarGradient f z⟫-q z*u.1 z*smoothScalarValue f z ∂(μ : Measure NormalBundle) := by
  unfold surfaceJacobiB
  rw [L2.inner_def,L2.inner_def,← integral_sub
    (L2.integrable_inner u.2 (surfaceSmoothJet μ f).2)
    (L2.integrable_inner (surfaceMultiplier μ q u.1) (surfaceSmoothJet μ f).1)]
  apply integral_congr_ae
  filter_upwards [(smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
    (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
    Lp.coeFn_lpSMul (r := 2) q u.1] with z hf hg hq
  change (surfaceSmoothJet μ f).1 z=smoothScalarValue f z at hf
  change (surfaceSmoothJet μ f).2 z=smoothScalarGradient f z at hg
  change (surfaceMultiplier μ q u.1) z=_ at hq
  simp only [hf,hg,hq,smul_eq_mul,Pi.mul_apply,
    RCLike.inner_apply,RCLike.conj_to_real]
  ring

lemma periodicGraphScalar_zero_jet (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : NormalBundle)
    (hz : (z.1 : Cover)∉tsupport χ) :
    smoothScalarValue (periodicGraphScalar a n hχ hc hψ) z=0 ∧
    smoothScalarGradient (periodicGraphScalar a n hχ hc hψ) z=0 := by
  have he := periodicGraphScalar_zero_germ a n hχ hc hO hψ z.1 hz
  refine ⟨he.eq_of_nhds,?_⟩
  have hd := he.fderiv_eq (𝕜 := ℝ)
  change gradient (periodicGraphScalar a n hχ hc hψ).val z.1-
    ⟪(z.2 : Cover),gradient (periodicGraphScalar a n hχ hc hψ).val z.1⟫ • (z.2 : Cover)=0
  simp [gradient,hd]

lemma surfaceJacobiB_periodicGraphScalar_weight (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u : SurfaceJet μ)
    (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {φ : Cover → ℝ} (hunit : ∀ x∈tsupport χ,φ x=1) :
    surfaceJacobiB μ q u (surfaceSmoothJet μ (periodicGraphScalar a n hχ hc hψ))=
      ∫ z,φ z.1*(⟪u.2 z,smoothScalarGradient (periodicGraphScalar a n hχ hc hψ) z⟫-
        q z*u.1 z*smoothScalarValue (periodicGraphScalar a n hχ hc hψ) z) ∂(μ : Measure NormalBundle) := by
  rw [surfaceJacobiB_smooth_integral]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : (z.1 : Cover)∈tsupport χ
  · rw [hunit _ hz,one_mul]
  · obtain ⟨hv,hg⟩ := periodicGraphScalar_zero_jet a n hχ hc hO hψ z hz
    simp only [hv,hg,inner_zero_right,mul_zero,sub_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceJacobiB_chart_form (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u : SurfaceJet μ)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} (hg : Continuous g)
    {φ : Cover → ℝ} (hφ : Measurable φ) (hφ0 : ∀ x,0≤φ x)
    (hφO : tsupport φ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    (hm : (μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    (hgc : ∀ y,φ (a+normalGraph n g y)≠0 → DifferentiableAt ℝ g y)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ,φ x=1)
    {S : Set Plane} (hS : IsOpen S)
    (hunit : ∀ y∈S,χ (a+normalGraph n g y)=1)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : tsupport ψ⊆S) :
    surfaceJacobiB μ q u (surfaceSmoothJet μ (periodicGraphScalar a n hχ hc hψ))=
      ∫ y in S,(cmcWeight (gradient g y))^2*
        ⟪graphCovector n g y (u.2 (actualNormalGraphChart a hn g y)),
          cmcJacobian (gradient g y) (gradient ψ y)⟫-
        cmcWeight (gradient g y)*q (actualNormalGraphChart a hn g y)*
          u.1 (actualNormalGraphChart a hn g y)*ψ y := by
  let f := periodicGraphScalar a n hχ hc hψ
  have hF : AEStronglyMeasurable (fun z => ⟪u.2 z,smoothScalarGradient f z⟫-
        q z*u.1 z*smoothScalarValue f z) (μ : Measure NormalBundle) :=
    (Lp.aestronglyMeasurable u.2 |>.inner (smoothScalarGradient f).continuous.aestronglyMeasurable).sub
      (((Lp.aestronglyMeasurable q).mul (Lp.aestronglyMeasurable u.1)).mul
        (smoothScalarValue f).continuous.aestronglyMeasurable)
  rw [surfaceJacobiB_periodicGraphScalar_weight μ q u a n hχ hc hχO hψ hφχ,
    graph_area_integral a hn hg hφ hφ0 hm hF,← integral_indicator hS.measurableSet]
  apply integral_congr_ae
  filter_upwards [] with y
  have hφS {y : Plane} (hy : y∈S) : φ (a+normalGraph n g y)=1 := by
    apply hφχ
    apply subset_tsupport
    rw [Function.mem_support,hunit y hy]
    exact one_ne_zero
  by_cases hyφ : φ (a+normalGraph n g y)=0
  · have hyS : y∉S := by intro hy; have := hφS hy; exact zero_ne_one (hyφ.symm.trans this)
    simp only [hyφ,zero_mul,indicator_of_notMem hyS]
  · have hypos : ∀ i,(a+normalGraph n g y) i∈Icc 0 1 := by
      have hx : a+normalGraph n g y∈tsupport φ := subset_tsupport _ hyφ
      exact fun i => ⟨(hφO hx i).1.le,(hφO hx i).2.le⟩
    have hv := periodicGraphScalar_graph_value a hn hχ hc hχO hψ hg hS hunit hs hypos
    have hgrad := periodicGraphScalar_graph_covector a hn hχ hc hχO hψ hg hS hunit hs
      (hgc y hyφ) hypos
    have ht := smoothScalarGradient_tangent f (actualNormalGraphChart a hn g y)
    rw [actualNormalGraphChart_normal] at ht
    rw [graphCovector_metric_pairing hn g y _ _ ht,hgrad,hv,graphAreaVector_norm_sqrt hn]
    change φ (a+normalGraph n g y)*cmcWeight (gradient g y)*
      (cmcWeight (gradient g y)*⟪_,_⟫-_*_*ψ y)=_
    by_cases hyS : y∈S
    · rw [indicator_of_mem hyS,hφS hyS]
      ring
    · have hyψ : y∉tsupport ψ := fun h => hyS (hs h)
      have hgz : gradient ψ y=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hyψ]
      rw [indicator_of_notMem hyS,image_eq_zero_of_notMem_tsupport hyψ,hgz,map_zero,inner_zero_right]
      ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_measure_scalar_test_integrable {ν : Measure Plane} (u : Lp ℝ 2 ν)
    {ψ : Plane → ℝ} (hψ : MemLp ψ 2 ν) : Integrable (fun y => u y*ψ y) ν :=
  (Lp.memLp u).integrable_mul hψ

lemma L2_measure_vector_test_integrable {ν : Measure Plane} (G : Lp Plane 2 ν)
    {F : Plane → Plane} (hF : MemLp F 2 ν) : Integrable (fun y => ⟪G y,F y⟫) ν := by
  apply (L2.integrable_inner (𝕜 := ℝ) G (hF.toLp F)).congr
  filter_upwards [hF.coeFn_toLp] with y hy
  exact congrArg (inner ℝ (G y)) hy

theorem PlaneWeakGradientOn.vector_ibp {S : Set Plane}
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G)
    {F : Plane → Plane} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hc : HasCompactSupport F) (hs : tsupport F⊆S) :
    (∫ y in S,⟪G y,F y⟫)= -(∫ y in S,u y*planeDivergence F y) := by
  let e (i : Fin 2) : Plane := EuclideanSpace.single i 1
  let D (i : Fin 2) : Plane → ℝ := fun y => F y i
  have hD (i) : ContDiff ℝ (⊤ : ℕ∞) (D i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hF
  have hsD (i) : tsupport (D i)⊆tsupport F := by
    apply closure_mono
    intro y hy
    change F y≠0
    intro hz
    apply hy
    change F y i=0
    rw [hz]
    rfl
  have hcD (i) : HasCompactSupport (D i) := hc.of_isClosed_subset (isClosed_tsupport _) (hsD i)
  have hi (i) : Integrable (fun y => G y i*F y i) (volume.restrict S) := by
    exact ((EuclideanSpace.proj i : Plane →L[ℝ] ℝ).comp_memLp G).integrable_mul
      (((hD i).continuous.memLp_of_hasCompactSupport (p := 2) (hcD i)).mono_measure Measure.restrict_le_self)
  have hj (i) : Integrable (fun y => u y*fderiv ℝ (D i) y (e i)) (volume.restrict S) :=
    L2_measure_scalar_test_integrable u
      ((((hD i).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        ((hcD i).fderiv_apply ℝ (e i)) |>.mono_measure Measure.restrict_le_self)
  have he (i) := hw (e i) (D i) (hD i) (hcD i) ((hsD i).trans hs)
  simp only [e,EuclideanSpace.inner_single_right,conj_trivial,one_mul,D] at he
  have hj' (i) : Integrable (fun y => u y*(fderiv ℝ F y (e i)) i) (volume.restrict S) := by
    simpa only [D,plane_component_fderiv (hF.of_le (by simp))] using hj i
  simp_rw [plane_component_fderiv (hF.of_le (by simp))] at he
  simp_rw [plane_inner_components,planeDivergence,mul_add]
  rw [integral_add (hi 0) (hi 1),integral_add (hj' 0) (hj' 1),he 0,he 1]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeDivergence_hasCompactSupport {F : Plane → Plane}
    (hc : HasCompactSupport F) : HasCompactSupport (planeDivergence F) := by
  apply hc.mono'
  intro y hy
  by_contra hys
  have hz := fderiv_of_notMem_tsupport ℝ hys
  apply hy
  simp [planeDivergence,hz]

theorem PlaneWeakGradientOn.ground_state {S : Set Plane}
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G)
    {A : Plane → Plane →L[ℝ] Plane} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAs : ∀ y v w,⟪v,A y w⟫=⟪w,A y v⟫)
    {q ψ : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆S) :
    (∫ y in S,(q y)^2*⟪G y,A y (gradient ψ y)⟫-
      q y*planeDivergence (fun z => A z (gradient q z)) y*u y*ψ y)=
    ∫ y in S,⟪q y • G y+u y • gradient q y,
      A y (gradient (fun z => q z*ψ z) y)⟫ := by
  have hgq := plane_gradient_contDiff hq
  have hgψ := plane_gradient_contDiff hψ
  let H : Plane → Plane := fun y => A y (gradient q y)
  let F : Plane → Plane := fun y => (q y*ψ y) • H y
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hA.clm_apply hgq
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (hq.mul hψ).smul hH
  have hcF : HasCompactSupport F := hc.mul_left.smul_right
  have hsF : tsupport F⊆S :=
    (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_right.trans hs)
  have hibp := hw.vector_ibp hF hcF hsF
  have hiF : Integrable (fun y => ⟪G y,F y⟫) (volume.restrict S) :=
    L2_measure_vector_test_integrable G
      ((hF.continuous.memLp_of_hasCompactSupport hcF).mono_measure Measure.restrict_le_self)
  have hiD : Integrable (fun y => u y*planeDivergence F y) (volume.restrict S) :=
    L2_measure_scalar_test_integrable u
      (((planeDivergence_continuous (hF.of_le (by simp))).memLp_of_hasCompactSupport
        (planeDivergence_hasCompactSupport hcF)).mono_measure Measure.restrict_le_self)
  let V : Plane → Plane := fun y => (q y)^2 • A y (gradient ψ y)
  have hV : ContDiff ℝ (⊤ : ℕ∞) V := (hq.pow 2).smul (hA.clm_apply hgψ)
  have hcV : HasCompactSupport V := by
    apply hc.mono'
    intro y hy
    by_contra hys
    have hz : gradient ψ y=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hys]
    apply hy
    simp [V,hz]
  have hiV : Integrable (fun y => (q y)^2*⟪G y,A y (gradient ψ y)⟫)
      (volume.restrict S) := by
    simpa only [V,real_inner_smul_right] using L2_measure_vector_test_integrable G
      ((hV.continuous.memLp_of_hasCompactSupport hcV).mono_measure Measure.restrict_le_self)
  have hiP : Integrable (fun y => q y*planeDivergence H y*u y*ψ y)
      (volume.restrict S) := by
    have hi := L2_measure_scalar_test_integrable u
      ((((hq.continuous.mul (planeDivergence_continuous (hH.of_le (by simp)))).mul
        hψ.continuous).memLp_of_hasCompactSupport hc.mul_left).mono_measure
          (ν := volume.restrict S) Measure.restrict_le_self)
    apply hi.congr
    filter_upwards [] with y
    simp only [Pi.mul_apply]
    ring
  have hpoint (y : Plane) :
      ⟪q y • G y+u y • gradient q y,A y (gradient (fun z => q z*ψ z) y)⟫=
      ((q y)^2*⟪G y,A y (gradient ψ y)⟫-q y*planeDivergence H y*u y*ψ y)+
        (⟪G y,F y⟫+u y*planeDivergence F y) := by
    have hdq := hq.differentiable (by simp) y
    have hdψ := hψ.differentiable (by simp) y
    have hdiv : planeDivergence F y=(q y*ψ y)*planeDivergence H y+
        ⟪gradient (fun z => q z*ψ z) y,H y⟫ :=
      planeDivergence_smul (hdq.mul hdψ) (hH.differentiable (by simp) y)
    rw [hdiv,plane_gradient_mul hdq hdψ]
    simp only [F,map_add,map_smul,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right,H]
    rw [hAs y (gradient q y) (gradient ψ y)]
    ring
  simp_rw [hpoint]
  have hsum := integral_add (hiV.sub hiP) (hiF.add hiD)
  have hsum2 := integral_add hiF hiD
  simp only [Pi.add_apply,Pi.sub_apply] at hsum hsum2
  rw [hsum,hsum2,hibp]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma PlaneWeakGradientOn.toWeakGradient {S : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (hw : PlaneWeakGradientOn S u G) : PlaneWeakGradient S u G := by
  intro v ψ hψ hc hs
  have h₁ : (∫ y in S,⟪G y,v⟫*ψ y)=(∫ y,⟪G y,v⟫*ψ y) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hs h)),mul_zero]
  have h₂ : (∫ y in S,u y*fderiv ℝ ψ y v)=(∫ y,u y*fderiv ℝ ψ y v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hy (hs h))]
    simp
  rw [← h₁,← h₂]
  exact hw v ψ hψ hc hs

lemma L2_measure_direction_test_integrable {S : Set Plane}
    (G : Lp Plane 2 (volume.restrict S)) (v : Plane) {ψ : Plane → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun y => ⟪G y,v⟫*ψ y) (volume.restrict S) := by
  have htest : MemLp (fun y => ψ y • v) 2 (volume.restrict S) :=
    ((hψ.smul continuous_const).memLp_of_hasCompactSupport hc.smul_right).mono_measure
      Measure.restrict_le_self
  apply (L2_measure_vector_test_integrable G htest).congr
  filter_upwards [] with y
  rw [real_inner_smul_right,mul_comm]

theorem PlaneWeakGradientOn.mul_smooth {S : Set Plane}
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G) {q : Plane → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    PlaneWeakGradientOn S (fun y => q y*u y)
      (fun y => q y • G y+u y • gradient q y) := by
  intro v ψ hψ hc hs
  let dq : Plane → ℝ := fun y => fderiv ℝ q y v
  let dψ : Plane → ℝ := fun y => fderiv ℝ ψ y v
  have hdq : Continuous dq := (hq.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi₁ := L2_measure_direction_test_integrable G v (hq.continuous.mul hψ.continuous) hc.mul_left
  simp only [Pi.mul_apply] at hi₁
  have hi₂ : Integrable (fun y => u y*(q y*dψ y)) (volume.restrict S) :=
    L2_measure_scalar_test_integrable u
      (((hq.continuous.mul hdψ).memLp_of_hasCompactSupport
        ((hc.fderiv_apply ℝ v).mul_left)).mono_measure Measure.restrict_le_self)
  have hi₃ : Integrable (fun y => u y*(ψ y*dq y)) (volume.restrict S) :=
    L2_measure_scalar_test_integrable u
      (((hψ.continuous.mul hdq).memLp_of_hasCompactSupport hc.mul_right).mono_measure
        Measure.restrict_le_self)
  have he := hw v (fun y => q y*ψ y) (hq.mul hψ) hc.mul_left
    (tsupport_mul_subset_right.trans hs)
  have he' : (∫ y in S,⟪G y,v⟫*(q y*ψ y))=
      -((∫ y in S,u y*(q y*dψ y))+(∫ y in S,u y*(ψ y*dq y))) := by
    rw [he,← integral_add hi₂ hi₃]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [fderiv_fun_mul (hq.differentiable (by simp) y) (hψ.differentiable (by simp) y),
      add_apply,smul_apply,smul_eq_mul,dq,dψ]
    ring
  have hleft : (∫ y in S,⟪q y • G y+u y • gradient q y,v⟫*ψ y)=
      (∫ y in S,⟪G y,v⟫*(q y*ψ y))+(∫ y in S,u y*(ψ y*dq y)) := by
    rw [← integral_add hi₁ hi₃]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [inner_add_left,real_inner_smul_left,inner_gradient_left,dq]
    ring
  rw [hleft,he']
  have hright : (∫ y in S,q y*u y*fderiv ℝ ψ y v)=(∫ y in S,u y*(q y*dψ y)) := by
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [dψ]
    ring
  rw [hright]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem PlaneWeakGradientOn.linearize {S : Set Plane}
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G)
    {A : Plane → Plane →L[ℝ] Plane} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAs : ∀ y v w,⟪v,A y w⟫=⟪w,A y v⟫)
    {q : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hq0 : ∀ y,q y≠0)
    (hJ : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y in S,(q y)^2*⟪G y,A y (gradient ψ y)⟫-
        q y*planeDivergence (fun z => A z (gradient q z)) y*u y*ψ y)=0) :
    ∀ η : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η⊆S → (∫ y,fderiv ℝ η y (A y (q y • G y+u y • gradient q y)))=0 := by
  intro η hη hc hs
  let ψ : Plane → ℝ := fun y => η y/q y
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hη.div hq hq0
  have hsψ : tsupport ψ⊆tsupport η := by
    apply closure_mono
    intro y hy
    change η y≠0
    intro hz
    apply hy
    simp [ψ,hz]
  have hcψ : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport _) hsψ
  have hefun : (fun z => q z*ψ z)=η := by
    funext z
    exact mul_div_cancel₀ _ (hq0 z)
  have he := hw.ground_state hA hAs hq hψ hcψ (hsψ.trans hs)
  rw [hJ ψ hψ hcψ (hsψ.trans hs),hefun] at he
  have hi : (∫ y in S,⟪q y • G y+u y • gradient q y,A y (gradient η y)⟫)=0 := he.symm
  rw [← hi]
  symm
  calc
    (∫ y in S,⟪q y • G y+u y • gradient q y,A y (gradient η y)⟫)=
        ∫ y in S,fderiv ℝ η y (A y (q y • G y+u y • gradient q y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hAs,inner_gradient_left]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hy (hs h))]
      rfl

theorem weak_cmc_graph_jacobi_linearization {S : Set Plane} (hS : IsOpen S)
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g) (fun _ => 0) S)
    (hJ : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y in S,(cmcWeight (gradient g y))^2*
        ⟪G y,cmcJacobian (gradient g y) (gradient ψ y)⟫-
        cmcWeight (gradient g y)*graphSquaredSecondFundamentalForm g y*u y*ψ y)=0) :
    ∀ η : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η⊆S →
      (∫ y,fderiv ℝ η y (cmcJacobian (gradient g y)
        (cmcWeight (gradient g y) • G y+
          u y • gradient (fun z => cmcWeight (gradient g z)) y)))=0 := by
  apply hw.linearize (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg))
    (fun y v w => (cmcJacobian_symmetric (gradient g y) v w).trans (real_inner_comm _ _))
    (cmcWeight_contDiff.comp (plane_gradient_contDiff hg))
    (fun y => (cmcWeight_pos _).ne')
  intro ψ hψ hc hs
  rw [← hJ ψ hψ hc hs]
  apply setIntegral_congr_fun hS.measurableSet
  intro y hy
  dsimp only [Function.comp_def]
  rw [cmc_graph_curvature_potential hg hS hlin hy]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_indicator_positive_piece {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) {D U C : Set X}
    (hU : IsOpen U) (hC : IsClosed C)
    (hDU : D={x | 0<f x}∩U) (hDC : D={x | 0<f x}∩C) :
    Continuous (D.indicator f) := by
  have hDo : IsOpen D := by rw [hDU]; exact (isOpen_lt continuous_const hf).inter hU
  have hclosureC : closure D⊆C := closure_minimal (by rw [hDC]; exact inter_subset_right) hC
  have hclosure0 : closure D⊆{x | 0≤f x} := by
    apply closure_minimal
    · intro x hx
      rw [hDC] at hx
      exact (show 0 < f x from hx.1).le
    · exact isClosed_le continuous_const hf
  apply continuous_indicator _ hf.continuousOn
  intro x hx
  have hxc := hclosureC (frontier_subset_closure hx)
  have hx0 := hclosure0 (frontier_subset_closure hx)
  have hxD : x∉D := by
    rw [hDo.frontier_eq] at hx
    exact hx.2
  have hxnp : ¬0<f x := by
    intro hpos
    apply hxD
    rw [hDC]
    exact ⟨hpos,hxc⟩
  exact le_antisymm (le_of_not_gt hxnp) hx0

theorem IsPositiveNodalPiece.continuous_value (f : smoothPeriodicScalars)
    {S D : Set Torus} (hD : IsPositiveNodalPiece f S D) :
    ContinuousOn (D.indicator (fun a => f.val (representative a))) S := by
  obtain ⟨⟨U,hU,hDU⟩,⟨C,hC,hDC⟩⟩ := hD
  let F : S → ℝ := fun a => f.val (representative a)
  let A : Set S := Subtype.val ⁻¹' D
  have hF : Continuous F :=
    (continuous_periodic_descent f.property.1.continuous f.property.2).comp continuous_subtype_val
  have hAU : A={a : S | 0<F a}∩(Subtype.val ⁻¹' U) := by
    ext a
    simp only [A,mem_preimage,hDU,mem_inter_iff,mem_ofPred_eq,F,a.property,true_and]
  have hAC : A={a : S | 0<F a}∩(Subtype.val ⁻¹' C) := by
    ext a
    simp only [A,mem_preimage,hDC,mem_inter_iff,mem_ofPred_eq,F,a.property,true_and]
  have hh := continuous_indicator_positive_piece hF
    (hU.preimage continuous_subtype_val) (hC.preimage continuous_subtype_val) hAU hAC
  rw [continuousOn_iff_continuous_domRestrict]
  convert hh using 1
  funext a
  by_cases ha : (a : Torus) ∈ D <;> simp [A, F, ha]

lemma nodalSurfaceValue_descent (f : smoothPeriodicScalars) (D : Set Torus) (z : NormalBundle) :
    nodalSurfaceValue f D z=
      D.indicator (fun a => f.val (representative a)) (normalProjection z) := by
  have hv : f.val (representative (normalProjection z))=f.val z.1 :=
    periodic_representative f.property.2 _
  by_cases hd : normalProjection z∈D
  · simp only [nodalSurfaceValue,indicator_of_mem (show z∈normalProjection ⁻¹' D from hd),
      indicator_of_mem hd,smoothScalarValue,ContinuousMap.coe_mk,hv]
  · simp [nodalSurfaceValue,hd]

end CubicTorus

end
end

end OAI
