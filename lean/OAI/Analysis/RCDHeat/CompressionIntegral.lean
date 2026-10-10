import Mathlib
import OAI.Analysis.RCDHeat.EntropyWassersteinGeodesic

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: CompressionIntegral, TestPlanMajorant, TestPlanRelaxed, TestPlanAE, GeodesicSubpath, TestPlanSubinterval. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

 theorem compression_weighted_integral_continuous (μ : Measure α) (ν : Measure β)
    (e : β → α) (he : Measurable e) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ν.map e ≤ C • μ) (w : β → ℝ) (hw : MemLp w 2 ν) :
    Continuous (fun f : Lp ℝ 2 μ => ∫y, w y*f (e y) ∂ν) := by
  have hcont := (continuous_const.inner (compressionPullback μ ν e he hC hcomp).continuous :
    Continuous (fun f : Lp ℝ 2 μ => inner ℝ (hw.toLp w)
      (compressionPullback μ ν e he hC hcomp f)))
  apply hcont.congr
  intro f
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hw.coeFn_toLp,compressionPullback_ae μ ν e he hC hcomp f] with y hy hf
  simp only [hy,hf,Real.inner_apply]

 theorem lp_integral_norm_continuous (ν : Measure β) [IsFiniteMeasure ν] :
    Continuous (fun f : Lp ℝ 2 ν => ∫y, ‖f y‖ ∂ν) := by
  let oneLp : Lp ℝ 2 ν := (memLp_const (1:ℝ)).toLp (fun _ => 1)
  have hnorm : LipschitzWith 1 (norm : ℝ → ℝ) := lipschitzWith_one_norm
  have hcont := (continuous_const.inner (hnorm.continuous_compLp norm_zero) :
    Continuous (fun f : Lp ℝ 2 ν => inner ℝ oneLp (hnorm.compLp norm_zero f)))
  apply hcont.congr
  intro f
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_const (1:ℝ) (μ := ν) (p := 2)).coeFn_toLp,
    hnorm.coeFn_compLp norm_zero f] with y hy hf
  change oneLp y = 1 at hy
  simp only [hy,hf,Function.comp_apply,Real.inner_apply,one_mul]

end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 theorem testPlan_slope_memLp (π : Measure C(Time,X)) [IsFiniteMeasure π]
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) :
    MemLp (fun z : ℝ × C(Time,X) => (localSlope φ (testPlanEval z)).toReal) 2 (testPlanMeasure π) := by
  let : IsFiniteMeasure (testPlanMeasure π) := by unfold testPlanMeasure; infer_instance
  apply (memLp_const (L:ℝ)).mono
    (((localSlope_measurable hφ.continuous).comp testPlanEval_measurable).ennreal_toReal.aestronglyMeasurable)
  filter_upwards with z
  simp only [Real.norm_of_nonneg ENNReal.toReal_nonneg,Real.norm_of_nonneg L.coe_nonneg]
  simpa only [Function.comp_apply,ENNReal.coe_toReal] using
    ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_of_lipschitz hφ (testPlanEval z))

omit [MeasurableSpace X] [BorelSpace X] in
 theorem testPlan_length_memLp (π : Measure C(Time,X)) [SFinite π]
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π) :
    MemLp (fun z : ℝ × C(Time,X) => dist (z.2 0) (z.2 1)) 2 (testPlanMeasure π) :=
  hD.comp_snd (volume.restrict (Icc (0:ℝ) 1))

 theorem testPlan_slope_majorized (μ : Measure X) (π : Measure C(Time,X)) [SFinite π]
    {C : ℝ≥0∞} (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    {φ : X → ℝ} {G : Lp ℝ 2 μ} (hG : IsSlopeMajorant μ φ G) :
    ∀ᵐ z ∂testPlanMeasure π, (localSlope φ (testPlanEval z)).toReal ≤ G (testPlanEval z) := by
  have hac := Measure.absolutelyContinuous_of_le_smul (testPlanMeasure_compression μ π hcomp)
  have hh := ae_of_ae_map testPlanEval_measurable.aemeasurable (hG.filter_mono hac.ae_le)
  filter_upwards [hh] with z hz
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hz.2
  rwa [ENNReal.toReal_ofReal hz.1] at h

 

 theorem lipschitz_testPlan_increment_le_majorant (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (u G : Lp ℝ 2 μ) (hu : ⇑u =ᵐ[μ] φ) (hG : IsSlopeMajorant μ φ G) :
    (∫γ : C(Time,X), |u (γ 1)-u (γ 0)| ∂π) ≤
      ∫z : ℝ × C(Time,X), dist (z.2 0) (z.2 1)*G (testPlanEval z) ∂testPlanMeasure π := by
  have hs := testPlan_slope_memLp π hφ
  have hd := testPlan_length_memLp π hD
  have hg := testPlanMeasure_eval_memLp μ π hC hcomp G
  have his := hd.integrable_mul hs
  have hig := hd.integrable_mul hg
  have hiu (t : Time) : MemLp (fun γ : C(Time,X) => u (γ t)) 2 π :=
    compressionPullback_memLp μ π (fun γ => γ t) (measurable_path_eval t) hC (hcomp t) u
  have hu' (t : Time) : ∀ᵐ γ ∂π, u (γ t) = φ (γ t) :=
    ae_of_ae_map (measurable_path_eval t).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hcomp t)).ae_eq hu)
  have hinc : Integrable (fun γ : C(Time,X) => |u (γ 1)-u (γ 0)|) π :=
    ((hiu 1).sub (hiu 0)).integrable (by norm_num) |>.abs
  calc
    _ ≤ ∫γ : C(Time,X), (∫t in Icc (0:ℝ) 1,
        dist (γ 0) (γ 1)*(localSlope φ (geodesicExtension γ t)).toReal) ∂π := by
      apply integral_mono_ae hinc his.integral_prod_right
      filter_upwards [hgeo,hu' 1,hu' 0] with γ hγ h1 h0
      change |u (γ 1)-u (γ 0)| ≤ ∫t in Icc (0:ℝ) 1,
        dist (γ 0) (γ 1)*(localSlope φ (geodesicExtension γ t)).toReal
      rw [h1,h0,integral_const_mul,integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le zero_le_one]
      exact hγ.increment_le_integral_localSlope hφ (show ((0:Time):ℝ) ≤ ((1:Time):ℝ) from zero_le_one)
    _ = ∫z : ℝ × C(Time,X), dist (z.2 0) (z.2 1)*
        (localSlope φ (testPlanEval z)).toReal ∂testPlanMeasure π :=
      (integral_prod_symm _ his).symm
    _ ≤ _ := by
      apply integral_mono_ae his hig
      filter_upwards [testPlan_slope_majorized μ π hcomp hG] with z hz
      exact mul_le_mul_of_nonneg_left hz dist_nonneg

end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 theorem testPlan_increment_continuous (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) :
    Continuous (fun u : Lp ℝ 2 μ => ∫γ : C(Time,X), |u (γ 1)-u (γ 0)| ∂π) := by
  let P (t : Time) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 π :=
    compressionPullback μ π (fun γ => γ t) (measurable_path_eval t) hC (hcomp t)
  have hc := (lp_integral_norm_continuous π).comp ((P 1).continuous.sub (P 0).continuous)
  apply hc.congr
  intro u
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (P 1 u) (P 0 u),
    compressionPullback_ae μ π (fun γ => γ 1) (measurable_path_eval 1) hC (hcomp 1) u,
    compressionPullback_ae μ π (fun γ => γ 0) (measurable_path_eval 0) hC (hcomp 0) u] with γ hs h1 h0
  change (P 1 u) γ = u (γ 1) at h1
  change (P 0 u) γ = u (γ 0) at h0
  simp only [hs,Pi.sub_apply,h1,h0,Real.norm_eq_abs]

 theorem testPlan_gradient_integral_continuous (μ : Measure X)
    (π : Measure C(Time,X)) [SFinite π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π) :
    Continuous (fun G : Lp ℝ 2 μ =>
      ∫z : ℝ × C(Time,X), dist (z.2 0) (z.2 1)*G (testPlanEval z) ∂testPlanMeasure π) :=
  compression_weighted_integral_continuous μ (testPlanMeasure π)
    testPlanEval testPlanEval_measurable hC (testPlanMeasure_compression μ π hcomp)
    _ (testPlan_length_memLp π hD)

 

 theorem IsRelaxedSlope.testPlan_increment (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) :
    (∫γ : C(Time,X), |u (γ 1)-u (γ 0)| ∂π) ≤
      ∫z : ℝ × C(Time,X), dist (z.2 0) (z.2 1)*G (testPlanEval z) ∂testPlanMeasure π := by
  obtain ⟨us,gs,Gs,hl,ha,hm,hu,hg⟩ := hG
  apply le_of_tendsto_of_tendsto
    ((testPlan_increment_continuous μ π hC hcomp).continuousAt.tendsto.comp hu)
    ((testPlan_gradient_integral_continuous μ π hC hcomp hD).continuousAt.tendsto.comp hg)
  apply Eventually.of_forall
  intro i
  obtain ⟨L,hL⟩ := hl i
  exact lipschitz_testPlan_increment_le_majorant μ π hgeo hC hcomp hD hL
    (us i) (Gs i) (ha i) (hm i)


 
 theorem IsRelaxedSlope.testPlan_ae_increment (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) :
    ∀ᵐ γ ∂π, |u (γ 1)-u (γ 0)| ≤
      dist (γ 0) (γ 1)*(∫t in Icc (0:ℝ) 1, G (geodesicExtension γ t)) := by
  have hiu (t : Time) : MemLp (fun γ : C(Time,X) => u (γ t)) 2 π :=
    compressionPullback_memLp μ π (fun γ => γ t) (measurable_path_eval t) hC (hcomp t) u
  have hi : Integrable (fun γ : C(Time,X) => |u (γ 1)-u (γ 0)|) π :=
    ((hiu 1).sub (hiu 0)).integrable (by norm_num) |>.abs
  have hd := testPlan_length_memLp π hD
  have hg := testPlanMeasure_eval_memLp μ π hC hcomp G
  have hig := hd.integrable_mul hg
  have hj : Integrable (fun γ : C(Time,X) =>
      dist (γ 0) (γ 1)*(∫t in Icc (0:ℝ) 1, G (geodesicExtension γ t))) π := by
    have hh := hig.integral_prod_right
    simpa only [Pi.mul_apply,testPlanEval,integral_const_mul] using hh
  apply ae_le_of_forall_setIntegral_le hi hj
  intro A _ _
  have hAc (t : Time) : (π.restrict A).map (fun γ => γ t) ≤ C • μ :=
    (Measure.map_mono π.restrict_le_self (measurable_path_eval t)).trans (hcomp t)
  have hAD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 (π.restrict A) :=
    hD.mono_measure π.restrict_le_self
  have h := hG.testPlan_increment μ (π.restrict A)
    (hgeo.filter_mono (ae_mono π.restrict_le_self)) hC hAc hAD
  have hiA := (testPlan_length_memLp (π.restrict A) hAD).integrable_mul
    (testPlanMeasure_eval_memLp μ (π.restrict A) hC hAc G)
  rw [show (∫z : ℝ × C(Time,X), dist (z.2 0) (z.2 1)*G (testPlanEval z)
      ∂testPlanMeasure (π.restrict A)) =
      ∫γ : C(Time,X), (∫t in Icc (0:ℝ) 1,
        dist (γ 0) (γ 1)*G (geodesicExtension γ t)) ∂π.restrict A from
      integral_prod_symm _ hiA] at h
  simpa only [integral_const_mul] using h

end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X]

 def timeSegment (s t : Time) : C(Time,Time) where
  toFun r := ⟨(1-(r:ℝ))*(s:ℝ)+(r:ℝ)*(t:ℝ), by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr r.property.2) s.property.1)
        (mul_nonneg r.property.1 t.property.1)
    · nlinarith only [mul_nonneg (sub_nonneg.mpr r.property.2) (sub_nonneg.mpr s.property.2),
        mul_nonneg r.property.1 (sub_nonneg.mpr t.property.2)]⟩
  continuous_toFun := by fun_prop

@[simp] theorem timeSegment_zero (s t : Time) : timeSegment s t 0 = s := by
  apply Subtype.ext
  simp [timeSegment]
@[simp] theorem timeSegment_one (s t : Time) : timeSegment s t 1 = t := by
  apply Subtype.ext
  simp [timeSegment]

 def subpath (s t : Time) (γ : C(Time,X)) : C(Time,X) := γ.comp (timeSegment s t)

@[simp] theorem subpath_zero (s t : Time) (γ : C(Time,X)) : subpath s t γ 0 = γ s := by
  simp [subpath]
@[simp] theorem subpath_one (s t : Time) (γ : C(Time,X)) : subpath s t γ 1 = γ t := by
  simp [subpath]

 theorem subpath_continuous (s t : Time) : Continuous (subpath (X := X) s t) :=
  ContinuousMap.continuous_precomp _

 theorem IsGeodesic.subpath {γ : C(Time,X)} (hγ : IsGeodesic γ) (s t : Time) :
    IsGeodesic (subpath s t γ) := by
  intro a b
  rw [subpath_zero,subpath_one,hγ s t]
  change dist (γ (timeSegment s t a)) (γ (timeSegment s t b)) = _
  rw [hγ]
  change |(1-(a:ℝ))*(s:ℝ)+(a:ℝ)*(t:ℝ)-((1-(b:ℝ))*(s:ℝ)+(b:ℝ)*(t:ℝ))| * _ = _
  rw [show (1-(a:ℝ))*(s:ℝ)+(a:ℝ)*(t:ℝ)-((1-(b:ℝ))*(s:ℝ)+(b:ℝ)*(t:ℝ)) =
    ((a:ℝ)-(b:ℝ))*((t:ℝ)-(s:ℝ)) by ring, abs_mul,abs_sub_comm (t:ℝ) (s:ℝ)]
  ring

variable [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
 theorem subpath_measurable (s t : Time) : Measurable (subpath (X := X) s t) :=
  (subpath_continuous s t).measurable

 theorem subpath_map_eval (π : Measure C(Time,X)) (s t r : Time) :
    (π.map (subpath s t)).map (fun γ => γ r) = π.map (fun γ => γ (timeSegment s t r)) := by
  rw [Measure.map_map (measurable_path_eval r) (subpath_measurable s t)]
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
 theorem testPlan_subpath_length_memLp (π : Measure C(Time,X))
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π) (s t : Time) :
    MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 (π.map (subpath s t)) := by
  apply (memLp_map_measure_iff ((continuous_eval_const 0).dist
    (continuous_eval_const 1)).aestronglyMeasurable (subpath_measurable s t).aemeasurable).mpr
  apply (hD.const_mul |(s:ℝ)-(t:ℝ)|).ae_eq
  filter_upwards [hgeo] with γ hγ
  simp only [Function.comp_apply,subpath_zero,subpath_one,hγ s t]

end

 
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X]

 theorem subpath_extension (s t : Time) (γ : C(Time,X)) {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    geodesicExtension (subpath s t γ) r =
      geodesicExtension γ ((1-r)*(s:ℝ)+r*(t:ℝ)) := by
  have he := geodesicExtension_eq γ (timeSegment s t ⟨r,hr⟩)
  change geodesicExtension (subpath s t γ) ((⟨r,hr⟩:Time):ℝ) = _
  rw [geodesicExtension_eq]
  exact he.symm

 theorem subpath_integral (s t : Time) (γ : C(Time,X)) (G : X → ℝ)
    (hst : (s:ℝ) ≤ (t:ℝ)) :
    |(s:ℝ)-(t:ℝ)| *(∫r in Icc (0:ℝ) 1, G (geodesicExtension (subpath s t γ) r)) =
      ∫r in (s:ℝ)..(t:ℝ), G (geodesicExtension γ r) := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le zero_le_one]
  have he : (∫r in (0:ℝ)..1, G (geodesicExtension (subpath s t γ) r)) =
      ∫r in (0:ℝ)..1, G (geodesicExtension γ ((s:ℝ)+((t:ℝ)-(s:ℝ))*r)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le zero_le_one] at hr
    dsimp only
    rw [subpath_extension s t γ hr]
    congr 2
    ring
  rw [he,abs_of_nonpos (sub_nonpos.mpr hst)]
  have h := intervalIntegral.smul_integral_comp_add_mul
    (fun r => G (geodesicExtension γ r)) ((t:ℝ)-(s:ℝ)) (s:ℝ) (a := 0) (b := 1)
  simpa only [smul_eq_mul,mul_zero,add_zero,mul_one,add_sub_cancel,neg_sub] using h

 theorem isClosed_geodesicSet : IsClosed {γ : C(Time,X) | IsGeodesic γ} := by
  simp only [IsGeodesic,ofPred_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_iInter
  intro t
  exact isClosed_eq ((continuous_eval_const s).dist (continuous_eval_const t))
    (continuous_const.mul ((continuous_eval_const 0).dist (continuous_eval_const 1)))

variable [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 

 theorem IsRelaxedSlope.testPlan_ae_subinterval (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G)
    (s t : Time) (hst : (s:ℝ) ≤ (t:ℝ)) :
    ∀ᵐ γ ∂π, |u (γ t)-u (γ s)| ≤
      dist (γ 0) (γ 1)*(∫r in (s:ℝ)..(t:ℝ), G (geodesicExtension γ r)) := by
  let ρ := π.map (subpath s t)
  let : IsFiniteMeasure ρ := Measure.isFiniteMeasure_map π (subpath s t)
  have hρgeo : ∀ᵐ γ ∂ρ, IsGeodesic γ := by
    apply (ae_map_iff (subpath_measurable s t).aemeasurable (by
      exact (isClosed_geodesicSet (X := X)).measurableSet)).mpr
    filter_upwards [hgeo] with γ hγ
    exact hγ.subpath s t
  have hρcomp (r : Time) : ρ.map (fun γ => γ r) ≤ C • μ := by
    rw [show ρ = π.map (subpath s t) from rfl,subpath_map_eval]
    exact hcomp _
  have hh := hG.testPlan_ae_increment μ ρ hρgeo hC hρcomp
    (testPlan_subpath_length_memLp π hgeo hD s t)
  have hh' := ae_of_ae_map (subpath_measurable s t).aemeasurable hh
  filter_upwards [hh',hgeo] with γ hγ hge
  simp only [subpath_one,subpath_zero] at hγ
  rw [hge s t] at hγ
  calc
    _ ≤ _ := hγ
    _ = dist (γ 0) (γ 1) * (|(s:ℝ)-(t:ℝ)| *
        (∫r in Icc (0:ℝ) 1, G (geodesicExtension (subpath s t γ) r))) := by ring
    _ = _ := by rw [subpath_integral s t γ G hst]


end RegularPointCoordinates

end OAI
