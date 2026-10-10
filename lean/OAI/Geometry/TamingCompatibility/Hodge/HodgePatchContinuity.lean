import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.FourthMomentKernel
import OAI.Geometry.TamingCompatibility.Hodge.HodgeActualAngular

namespace OAI

section

noncomputable section
namespace TamingCompatibility.ManifoldKernelExtension
open Set
open scoped Manifold
variable {E X G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [ChartedSpace E X] [T2Space X] [NormedAddCommGroup G]
lemma push_continuous (p : X) (f : E × E → G) (K : Set (E × E)) (hc : IsCompact K)
    (hK : K ⊆ (extChartAt 𝓘(ℝ,E) p).target ×ˢ (extChartAt 𝓘(ℝ,E) p).target)
    (hf : Function.support f ⊆ K) (hcont : Continuous f) : Continuous (push p f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have h := push_joint_continuousAt (P := Unit) p (fun _ => f) K hc hK (fun _ => hf) ()
    (fun z => (hcont.comp continuous_snd).continuousAt (x := ((),z))) x
  exact h.comp (continuous_const.prodMk continuous_id).continuousAt
end TamingCompatibility.ManifoldKernelExtension

namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

include hs hE in
lemma gammaLeadingMatrix_continuous {r : ℝ} (hr : 0 < r) (T : ℝ) (p : A.centers) :
    Continuous (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p)) := by
  obtain ⟨M,L,hM,hL,hbound⟩ := leadingMatrix_gaussian J α ht A E hE hs p
  let C := M*((4*Real.pi*L)⁻¹)^2
  let ν := volume.restrict (Ioc 0 (T/r^2))
  let G := fun (z : Space × Space) (s : ℝ) => hodgeGammaWeight s • leadingMatrix J α ht A E p (r^2*s) z
  let m := fun s : ℝ => C/r^4*(Real.exp (-s)*s^3)
  have hm : Integrable m ν := by
    have h := HodgeKernelBounds.polynomialMoment_integrable 3 0
    simp only [pow_zero,mul_one] at h
    exact (h.mono_set (fun _ h => h.1)).const_mul _
  have hGb (z : Space × Space) : ∀ᵐ s ∂ν, ‖G z s‖ ≤ m s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs'
    have htp := mul_pos (sq_pos_of_pos hr) hs'.1
    have hb : VolterraBounds.weight 0 (r^2*s) z.1 z.2 *
        ‖leadingMatrix J α ht A E p (r^2*s) z‖ ≤ C/(r^2*s)^2 := by
      simp only [VolterraBounds.weight,pow_zero,one_mul]
      exact (hbound _ htp z.1 z.2).trans ((mul_le_mul_of_nonneg_left
        (FlatHeat.heat_time_bound hL htp _) hM).trans_eq (by dsimp [C]; ring))
    simpa only [VolterraBounds.weight,pow_zero,one_mul,mul_one] using
      HodgeKernelBounds.weighted_gamma_integrand 3 2 0 (by norm_num) hr hs'.1
        (fun t q y => leadingMatrix J α ht A E p t (q,y)) z.1 z.2 hb
  have hGc : ∀ᵐ s ∂ν, Continuous (fun z => G z s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs'
    change Continuous (fun z => hodgeGammaWeight s • leadingMatrix J α ht A E p (r^2*s) z)
    have hc : Continuous (leadingMatrix J α ht A E p (r^2*s)) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      exact (leadingMatrix_smooth J α ht A E hE hs p
        (mul_pos (sq_pos_of_pos hr) hs'.1) z).continuousAt.comp
          (continuousAt_const.prodMk continuousAt_id)
    exact hc.const_smul (hodgeGammaWeight s)
  have hGm (z : Space × Space) : AEStronglyMeasurable (G z) ν :=
    (leadingMatrix_gamma_integrable J α ht A E hr T p z).aestronglyMeasurable
  have h := (continuous_of_dominated hGm hGb hm hGc).const_smul (1/120 : ℝ)
  have he (z : Space × Space) : (1/120 : ℝ) • (∫ s, G z s ∂ν) =
      coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p) z :=
    leadingMatrix_gamma J α ht A E hr T p z
  change Continuous (fun z => (1/120 : ℝ) • (∫ s, G z s ∂ν)) at h
  simpa only [he] using h

include hs hE in
lemma gammaLeadingPatch_continuous {r : ℝ} (hr : 0 < r) (T : ℝ) (p : A.centers) :
    Continuous (ManifoldKernelExtension.push p.val
      (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p))) :=
  ManifoldKernelExtension.push_continuous p.val _ (E p).physicalCompact
    (E p).physicalCompact_compact (physicalCompact_target J α ht A E p)
    ((coordinateMatrix_support J α ht A E p _).trans (gammaPartitionLeading_support J α ht A E hE T r p))
    (gammaLeadingMatrix_continuous A J α hs ht E hE hr T p)

def gammaPatchWedge (T r : ℝ) (p : A.centers)
    (u v : MetricUnit (hermitianMetric J α hs ht)) : ℝ :=
  unitFrameFunctional A J α ht E (hermitianMetric J α hs ht) u
    (ManifoldKernelExtension.push p.val
      (coordinateMatrix J α ht A E p (gammaPartitionLeading J α ht A E T r p))
      (v.val.proj,u.val.proj) (unitStarDirection A J α ht E (hermitianMetric J α hs ht) v))

include hs hE in
lemma gammaPatchWedge_continuous {r : ℝ} (hr : 0 < r) (T : ℝ) (p : A.centers) :
    Continuous (fun uv : MetricUnit (hermitianMetric J α hs ht) × MetricUnit (hermitianMetric J α hs ht) =>
      gammaPatchWedge A J α hs ht E T r p uv.1 uv.2) := by
  have hb : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  exact ((unitFrameFunctional_continuous A J α hs ht E hE _).comp continuous_fst).clm_apply
    (((gammaLeadingPatch_continuous A J α hs ht E hE hr T p).comp
      ((hb.comp continuous_snd).prodMk (hb.comp continuous_fst))).clm_apply
        ((unitStarDirection_continuous A J α hs ht E hE _).comp continuous_snd))

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

abbrev UnitPair := MetricUnit (hermitianMetric J α hs ht) × MetricUnit (hermitianMetric J α hs ht)

def angularBase (uv : UnitPair J α hs ht) : X × X := (uv.2.val.proj,uv.1.val.proj)

omit [CompactSpace X] [T2Space X] in
lemma angularBase_continuous : Continuous (angularBase J α hs ht) := by
  have hb : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  exact (hb.comp continuous_snd).prodMk (hb.comp continuous_fst)

def angularDomain (p : A.centers) : Set (UnitPair J α hs ht) :=
  (angularBase J α hs ht) ⁻¹' ManifoldKernelExtension.liftSet p.val (E p).physicalCompact

def angularChartCoordinates (p : A.centers) (uv : UnitPair J α hs ht) : Space × Space :=
  (extChartAt Model p.val uv.2.val.proj,extChartAt Model p.val uv.1.val.proj)

def angularCoordinates (p : A.centers) (uv : UnitPair J α hs ht) : Space × Space :=
  (E p).normalChart.symm (angularChartCoordinates A J α hs ht p uv)

omit [CompactSpace X] in
lemma angularDomain_closed (p : A.centers) : _root_.IsClosed (angularDomain A J α hs ht E p) :=
  ((ManifoldKernelExtension.liftSet_compact p.val _ (E p).physicalCompact_compact
    (physicalCompact_target J α ht A E p)).isClosed).preimage (angularBase_continuous J α hs ht)

omit [CompactSpace X] [T2Space X] in
lemma angularChartCoordinates_mem (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    angularChartCoordinates A J α hs ht p uv ∈ (E p).physicalCompact := by
  obtain ⟨w,hw,he⟩ := huv
  have he' := congrArg (fun xy : X × X => (extChartAt Model p.val xy.1,extChartAt Model p.val xy.2)) he
  have ht' := physicalCompact_target J α ht A E p hw
  simp only [(extChartAt Model p.val).right_inv ht'.1,(extChartAt Model p.val).right_inv ht'.2] at he'
  change w = angularChartCoordinates A J α hs ht p uv at he'
  rw [← he']
  exact hw

omit [CompactSpace X] [T2Space X] in
lemma angularChartCoordinates_source (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    uv.2.val.proj ∈ (extChartAt Model p.val).source ∧ uv.1.val.proj ∈ (extChartAt Model p.val).source :=
  ManifoldKernelExtension.liftSet_source p.val _ (physicalCompact_target J α ht A E p) huv

omit [CompactSpace X] [T2Space X] in
lemma angularCoordinates_mem (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    angularCoordinates A J α hs ht E p uv ∈ (E p).normalCompact := by
  obtain ⟨z,hz,he⟩ := angularChartCoordinates_mem A J α hs ht E p huv
  unfold angularCoordinates
  rw [← he,(E p).normalChart.left_inv ((E p).normalCompact_source hz)]
  exact hz

omit [CompactSpace X] [T2Space X] in
lemma angularCoordinates_chart (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    (E p).normalChart (angularCoordinates A J α hs ht E p uv) =
      angularChartCoordinates A J α hs ht p uv := by
  apply (E p).normalChart.right_inv
  obtain ⟨z,hz,he⟩ := angularChartCoordinates_mem A J α hs ht E p huv
  rw [← he]
  exact (E p).normalChart.map_source ((E p).normalCompact_source hz)

omit [CompactSpace X] [T2Space X] in
lemma angularCoordinates_bases (p : A.centers) {uv : UnitPair J α hs ht}
    (huv : uv ∈ angularDomain A J α hs ht E p) :
    (extChartAt Model p.val).symm (normalMap (E p).metricExtension (E p).frameExtension
      (angularCoordinates A J α hs ht E p uv).1 (angularCoordinates A J α hs ht E p uv).2) = uv.1.val.proj ∧
    (extChartAt Model p.val).symm (angularCoordinates A J α hs ht E p uv).1 = uv.2.val.proj := by
  have he := angularCoordinates_chart A J α hs ht E p huv
  have hb := angularChartCoordinates_source A J α hs ht E p huv
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  change (angularCoordinates A J α hs ht E p uv).1 = extChartAt Model p.val uv.2.val.proj at he1
  change normalMap (E p).metricExtension (E p).frameExtension
    (angularCoordinates A J α hs ht E p uv).1 (angularCoordinates A J α hs ht E p uv).2 =
    extChartAt Model p.val uv.1.val.proj at he2
  rw [he2,he1]
  exact ⟨(extChartAt Model p.val).left_inv hb.2,(extChartAt Model p.val).left_inv hb.1⟩

omit [CompactSpace X] [T2Space X] in
lemma angularChartCoordinates_continuousOn (p : A.centers) :
    ContinuousOn (angularChartCoordinates A J α hs ht p) (angularDomain A J α hs ht E p) := by
  have hb := angularBase_continuous J α hs ht
  exact ((continuousOn_extChartAt p.val).comp hb.fst.continuousOn
      (fun _ h => (angularChartCoordinates_source A J α hs ht E p h).1)).prodMk
    ((continuousOn_extChartAt p.val).comp hb.snd.continuousOn
      (fun _ h => (angularChartCoordinates_source A J α hs ht E p h).2))

omit [CompactSpace X] [T2Space X] in
lemma angularCoordinates_continuousOn (p : A.centers) :
    ContinuousOn (angularCoordinates A J α hs ht E p) (angularDomain A J α hs ht E p) := by
  apply (E p).normalChart.symm.continuousOn.comp (angularChartCoordinates_continuousOn A J α hs ht E p)
  intro uv huv
  obtain ⟨z,hz,he⟩ := angularChartCoordinates_mem A J α hs ht E p huv
  rw [← he]
  exact (E p).normalChart.map_source ((E p).normalCompact_source hz)

def angularWeight (p : A.centers) (uv : UnitPair J α hs ht) : ℝ :=
  let z := angularCoordinates A J α hs ht E p uv
  coordinatePartition A p z.1 * (E p).normalCutoff z.2 *
    (normalAngular A J α hs ht E p z uv.1 uv.2)^2

omit [CompactSpace X] [T2Space X] in
lemma angularWeight_nonneg (p : A.centers) (uv : UnitPair J α hs ht) :
    0 ≤ angularWeight A J α hs ht E p uv := by
  apply mul_nonneg (mul_nonneg (coordinatePartition_bounds A p _).1 (E p).normalCutoff.nonneg) (sq_nonneg _)

include hE in
lemma angularWeight_continuousOn (p : A.centers) :
    ContinuousOn (angularWeight A J α hs ht E p) (angularDomain A J α hs ht E p) := by
  let z := angularCoordinates A J α hs ht E p
  have hz := angularCoordinates_continuousOn A J α hs ht E p
  have hy := angularChartCoordinates_continuousOn A J α hs ht E p
  have hg : ContinuousOn (fun uv => normalGauge J α ht p.val (E p).chart
      (E p).metricExtension (E p).frameExtension (z uv)) (angularDomain A J α hs ht E p) := by
    intro uv huv
    have hx := angularCoordinates_mem A J α hs ht E p huv
    have hn := (((E p).actual hx.1).center J α ht p.val (E p).chart
      (E p).metricExtension (E p).frameExtension).1
    change ((z uv).1,0) ∈ normalDomain J α ht p.val (E p).chart (E p).metricExtension (E p).frameExtension at hn
    have hhg : ContinuousAt (normalGauge J α ht p.val (E p).chart (E p).metricExtension
      (E p).frameExtension) (z uv) := (normalGauge_smooth J α ht p.val (E p).chart (E p).metricExtension
      (E p).frameExtension hs (E p).metric_smooth (E p).frame_smooth hn).continuousAt
    exact hhg.comp_continuousWithinAt (hz uv huv)
  have hdu := ((coordinateDecode_smooth J α ht A E hE hs p).continuousOn.comp hy.snd
    (fun uv huv => ((E p).physicalCompact_domain (angularChartCoordinates_mem A J α hs ht E p huv)).2)).clm_apply
      (((unitFrameDirection_continuous A J α hs ht E hE _).comp continuous_fst).continuousOn)
  have hdv := ((coordinateDecode_smooth J α ht A E hE hs p).continuousOn.comp hy.fst
    (fun uv huv => ((E p).physicalCompact_domain (angularChartCoordinates_mem A J α hs ht E p huv)).1)).clm_apply
      (((unitFrameDirection_continuous A J α hs ht E hE _).comp continuous_snd).continuousOn)
  have ha := (hdu.sub (hg.clm_apply hdv)).norm.pow 2
  have hw := (((coordinatePartition_smooth_compact A p).1.continuous.comp_continuousOn hz.fst).mul
    ((E p).normalCutoff.continuous.comp_continuousOn hz.snd)).mul ha
  apply hw.congr
  intro uv huv
  have he := angularCoordinates_chart A J α hs ht E p huv
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  change (z uv).1 = (angularChartCoordinates A J α hs ht p uv).1 at he1
  change normalMap (E p).metricExtension (E p).frameExtension (z uv).1 (z uv).2 =
    (angularChartCoordinates A J α hs ht p uv).2 at he2
  dsimp only [angularWeight,normalAngular,unitCoordinate,Function.comp_def,Pi.mul_apply,Pi.sub_apply,Pi.pow_apply]
  rw [he2,he1]

def angularNearSet (r : ℝ) (p : A.centers) : Set (UnitPair J α hs ht) :=
  angularDomain A J α hs ht E p ∩
    (fun uv => ‖(angularCoordinates A J α hs ht E p uv).2‖) ⁻¹' Iic r

omit [CompactSpace X] in
lemma angularNearSet_closed (r : ℝ) (p : A.centers) : _root_.IsClosed (angularNearSet A J α hs ht E r p) :=
  (angularCoordinates_continuousOn A J α hs ht E p).snd.norm.preimage_isClosed_of_isClosed
    (angularDomain_closed A J α hs ht E p) isClosed_Iic

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

def angularNear (r : ℝ) (p : A.centers) : UnitPair J α hs ht → ℝ :=
  (angularNearSet A J α hs ht E r p).indicator (angularWeight A J α hs ht E p)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
lemma angularNear_nonneg (r : ℝ) (p : A.centers) (uv : UnitPair J α hs ht) :
    0 ≤ angularNear A J α hs ht E r p uv :=
  Set.indicator_nonneg (fun v _ => angularWeight_nonneg A J α hs ht E p v) uv

include hE in
omit [MeasurableSpace X] [BorelSpace X] in
lemma angularNear_integrable (r : ℝ) (p : A.centers)
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsFiniteMeasure μ] :
    Integrable (angularNear A J α hs ht E r p) (μ.prod μ) := by
  have hc := angularNearSet_closed A J α hs ht E r p
  apply (integrable_indicator_iff hc.measurableSet).mpr
  exact ContinuousOn.integrableOn_compact hc.isCompact
    ((angularWeight_continuousOn A J α hs ht E hE p).mono inter_subset_left)

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
