import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeGlobalKernelContinuity

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

def kernelWeakAction (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (v : X → FrameSpace A) (a : TwoForm X) (t : ℝ) : ℝ :=
  ∫ y, ∫ x, framePairing A J α ht E a x (K t x y (v y)) ∂geometricVolume A J α ∂geometricVolume A J α

include hs hE in
lemma kernel_pairing_integral_continuousOn
    (K : ℝ → X → X → FrameSpace A →L[ℝ] FrameSpace A)
    (hK : ∀ t, 0 < t → ∀ x y, ContinuousAt
      (fun z : ℝ × (X × X) => K z.1 z.2.1 z.2.2) (t,(x,y)))
    (v : X → FrameSpace A) (hv : Continuous v) (a : TwoForm X) (ha : IsSmooth a) :
    ContinuousOn (fun z : ℝ × X => ∫ x, framePairing A J α ht E a x
      (K z.1 x z.2 (v z.2)) ∂geometricVolume A J α) {z | 0 < z.1} := by
  let := geometricVolume_finite A J α hs ht
  apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
  · intro z hz
    have hk := (hK z.1.1 hz.1 z.2 z.1.2).comp
      (f := fun w : (ℝ × X) × X => (w.1.1,(w.2,w.1.2)))
      (continuousAt_fst.fst.prodMk (continuousAt_snd.prodMk continuousAt_fst.snd))
    have hφ : ContinuousAt (fun w : (ℝ × X) × X => framePairing A J α ht E a w.2) z :=
      (framePairing_continuous A J α hs ht E hE a ha).continuousAt.comp
      (f := fun w : (ℝ × X) × X => w.2) continuousAt_snd
    exact (hφ.clm_apply (hk.clm_apply (hv.continuousAt.comp continuousAt_fst.snd))).continuousWithinAt
  · intro _ x _ hx
    exact (hx (mem_univ x)).elim

include hE in
lemma kernel_leading_pairing_hasDerivAt (y : X) (v : FrameSpace A)
    (a : PreL2 A J α hs ht true) {t : ℝ} (htp : 0 < t) :
    HasDerivAt (fun s => ∫ x, framePairing A J α ht E a.val x
        (globalLeading J α ht A E s x y v) ∂geometricVolume A J α)
      ((∫ x, framePairing A J α ht E a.val x
        (globalResidual J α ht A E t x y v) ∂geometricVolume A J α) -
       (∫ x, framePairing A J α ht E (hodgeLaplacian A J α hs ht a).val x
        (globalLeading J α ht A E t x y v) ∂geometricVolume A J α)) t := by
  have hh := leadingKernelForm_weak_laplacian A J α hs ht E hE y htp v a
  simp_rw [leadingKernelForm_pairing A J α ht E hE,
    residualKernelForm_pairing A J α ht E hE] at hh
  exact hh

attribute [local irreducible] framePairing globalLeading globalResidual hodgeLaplacian

include hE in
lemma kernelWeakAction_leading_hasDerivAt (v : X → FrameSpace A) (hv : Continuous v)
    (a : PreL2 A J α hs ht true) {t : ℝ} (htp : 0 < t) :
    HasDerivAt (kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val)
      (kernelWeakAction A J α ht E (globalResidual J α ht A E) v a.val t -
       kernelWeakAction A J α ht E (globalLeading J α ht A E) v
         (hodgeLaplacian A J α hs ht a).val t) t := by
  let := geometricVolume_finite A J α hs ht
  let F := fun s y => ∫ x, framePairing A J α ht E a.val x
    (globalLeading J α ht A E s x y (v y)) ∂geometricVolume A J α
  let R := fun s y => ∫ x, framePairing A J α ht E a.val x
    (globalResidual J α ht A E s x y (v y)) ∂geometricVolume A J α
  let L := fun s y => ∫ x, framePairing A J α ht E (hodgeLaplacian A J α hs ht a).val x
    (globalLeading J α ht A E s x y (v y)) ∂geometricVolume A J α
  have hF := kernel_pairing_integral_continuousOn A J α hs ht E hE _
    (fun _ hp x y => globalLeading_continuousAt A J α hs ht E hE hp x y) v hv a.val a.property
  have hR := kernel_pairing_integral_continuousOn A J α hs ht E hE _
    (fun _ hp x y => globalResidual_continuousAt A J α hs ht E hE hp x y) v hv a.val a.property
  have hL := kernel_pairing_integral_continuousOn A J α hs ht E hE _
    (fun _ hp x y => globalLeading_continuousAt A J α hs ht E hE hp x y) v hv
    (hodgeLaplacian A J α hs ht a).val (hodgeLaplacian A J α hs ht a).property
  have hFc (s : ℝ) (hp : 0 < s) : Continuous (F s) :=
    continuousOn_univ.mp (hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => hp))
  have hRc : Continuous (R t) :=
    continuousOn_univ.mp (hR.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => htp))
  have hLc : Continuous (L t) :=
    continuousOn_univ.mp (hL.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => htp))
  have hh := OperatorCalculus.hasDerivAt_integral_compact_positive (geometricVolume A J α)
    F (fun s y => R s y - L s y) univ isCompact_univ hFc
    ((hR.sub hL).mono (fun _ h => h.1))
    (fun _ _ _ _ => mem_univ _) (fun _ _ _ _ => mem_univ _) ?_ htp
  · rw [integral_sub (hRc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hLc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))] at hh
    exact hh
  · intro s hp y
    exact kernel_leading_pairing_hasDerivAt A J α hs ht E hE y (v y) a hp

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms NormalJets NormalMetricCalculus CoordinateOperator HodgeNormalSymbol
open FirstJetGauge OrthogonalJets Filter Set OperatorCalculus MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (ht : Tames α J)
  (p : X) (D : GeometricChart.Data J α ht p)
  (g : Space → MetricTensor (V := Space)) (B : Space → Space →L[ℝ] Space)
attribute [local irreducible] normalGauge normalFirst

lemma actual_cutoff_initial_local (hs : IsSmooth α) (hg : ContDiff ℝ ∞ g) (hB : ContDiff ℝ ∞ B)
    {q : Space} (hactual : ActualData J α ht p D q g B)
    (χ : Space → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : χ 0 = 1)
    {U : Set Space} (hU : IsOpen U) (hχU : tsupport χ ⊆ U)
    (u : W) (η : Space → W) (hη : ContDiffOn ℝ ∞ η U) :
    Tendsto (fun t : ℝ => ∫ z, normalDensity g B (q,z) * ⟪η z,
      normalGauge J α ht p D g B (q,z) (χ z • NormalHeatResidual.modelSection t u z)⟫)
      (𝓝[>] 0) (𝓝 ⟪η 0,u⟫) := by
  obtain ⟨η',hη',hc,hD,he⟩ := exists_compact_smooth_extension hU hχc hχU hη
  let F : Space → ℝ := fun z => normalDensity g B (q,z) * χ z *
    ⟪η' z,normalGauge J α ht p D g B (q,z) u⟫
  have hG : Continuous (fun z : Space => normalGauge J α ht p D g B (q,z)) :=
    continuous_iff_continuousAt.mpr (fun z =>
      ((normalGauge_smooth J α ht p D g B hs hg hB (hactual.center J α ht p D g B).1).comp z
        (contDiffAt_const.prodMk contDiffAt_id)).continuousAt)
  have hF : Continuous F := (((normalDensity_continuous g B hg hB).comp
    (continuous_const.prodMk continuous_id)).mul hχ).mul
      (hη'.continuous.inner (hG.clm_apply continuous_const))
  have hFc : HasCompactSupport F := by
    apply hχc.mono
    intro z hz
    change χ z ≠ 0
    intro hz0
    exact hz (by simp [F,hz0])
  have hzχ : (0 : Space) ∈ tsupport χ := subset_tsupport _ (by simpa only [Function.mem_support,hχ0] using one_ne_zero)
  have hF0 : F 0 = ⟪η 0,u⟫ := by
    simp only [F,normalDensity_zero J α ht p D g B hactual,hχ0,one_mul,
      normalGauge_zero,one_apply_eq_self,(he 0 hzχ).eq_of_nhds]
  have hh := FlatHeat.heat_approximate_identity F (hF.integrable_of_hasCompactSupport hFc) hF.continuousAt
  rw [hF0] at hh
  convert hh using 1
  funext t
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ tsupport χ
  · simp only [F,(he z hz).eq_of_nhds,NormalHeatResidual.modelSection,map_smul,
      inner_smul_right,smul_eq_mul]
    ring
  · simp only [F,image_eq_zero_of_notMem_tsupport hz,mul_zero,zero_mul,zero_smul,map_zero,
      inner_zero_right,smul_zero]

namespace ParametrixData
variable {J : AlmostComplexStructure X} {α : TwoForm X} {ht : Tames α J} {p : X}
  (E : ParametrixData J α ht p)

lemma cutoff_form_initial (hs : IsSmooth α) {q : Space}
    (hq : q ∈ Metric.closedBall (extChartAt Model p p) E.radius)
    (u : W) (a : TwoForm X) (ha : IsSmooth a) :
    Tendsto (fun t : ℝ => ∫ z, normalDensity E.metricExtension E.frameExtension (q,z) *
      ⟪HodgeChart.rawVector J α ht p E.chart a (normalMap E.metricExtension E.frameExtension q z),
        normalGauge J α ht p E.chart E.metricExtension E.frameExtension (q,z)
          (E.normalCutoff z • NormalHeatResidual.modelSection t u z)⟫)
      (𝓝[>] 0) (𝓝 ⟪HodgeChart.rawVector J α ht p E.chart a q,u⟫) := by
  have hh := actual_cutoff_initial_local J α ht p E.chart E.metricExtension E.frameExtension hs
    E.metric_smooth E.frame_smooth (E.actual hq) E.normalCutoff E.normalCutoff.continuous
    E.normalCutoff.hasCompactSupport
    (E.normalCutoff.one_of_mem_closedBall (Metric.mem_closedBall_self E.normalCutoff.rIn_pos.le))
    (E.weakSliceDomain_open q) (E.cutoff_weakSliceDomain hq) u _ (E.form_normal_smooth a ha q)
  simpa only [Function.comp_apply,normalMap_zero] using hh

end ParametrixData
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
