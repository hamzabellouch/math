import Mathlib
import OAI.Analysis.RCDHeat.CompressionIntegral
import OAI.Analysis.RCDHeat.EntropyWassersteinGeodesic

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: TestPlanContinuous, TestPlanDerivative, DenseACExtension, TestPlanClock, TestPlanRepresentative. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 theorem testPlan_eval_intervalIntegrable (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) (G : Lp ℝ 2 μ) :
    ∀ᵐ γ ∂π, IntervalIntegrable (fun r => G (geodesicExtension γ r)) volume 0 1 := by
  let : IsFiniteMeasure (testPlanMeasure π) := by unfold testPlanMeasure; infer_instance
  have hi := (testPlanMeasure_eval_memLp μ π hC hcomp G).integrable (show (1:ℝ≥0∞) ≤ 2 by norm_num)
  have hh := hi.prod_left_ae
  filter_upwards [hh] with γ hγ
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hγ

 theorem IsRelaxedSlope.testPlan_ae_distance (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) (s t : Time) :
    ∀ᵐ γ ∂π, dist (u (γ s)) (u (γ t)) ≤
      |dist (γ 0) (γ 1)*(∫r in (s:ℝ)..(t:ℝ), G (geodesicExtension γ r))| := by
  rcases le_total (s:ℝ) (t:ℝ) with hst | hts
  · filter_upwards [hG.testPlan_ae_subinterval μ π hgeo hC hcomp hD s t hst] with γ hγ
    simpa only [Real.dist_eq,abs_sub_comm] using hγ.trans (le_abs_self _)
  · filter_upwards [hG.testPlan_ae_subinterval μ π hgeo hC hcomp hD t s hts] with γ hγ
    have hh := hγ.trans (le_abs_self _)
    rw [intervalIntegral.integral_symm,mul_neg,abs_neg] at hh
    exact hh

noncomputable def rationalTime (q : ℚ) : Time := Set.projIcc 0 1 zero_le_one (q:ℝ)
 theorem rationalTime_dense : DenseRange rationalTime :=
  (Set.projIcc_surjective zero_le_one).denseRange.comp Rat.denseRange_cast
    (LipschitzWith.projIcc zero_le_one).continuous

 

 theorem IsRelaxedSlope.testPlan_ae_absolutelyContinuous (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G)
    {φ : X → ℝ} (hφ : Continuous φ) (hu : ⇑u =ᵐ[μ] φ) :
    ∀ᵐ γ ∂π, AbsolutelyContinuousOnInterval (fun r => φ (geodesicExtension γ r)) 0 1 ∧
      ∀ s t : Time, dist (φ (γ s)) (φ (γ t)) ≤
        |dist (γ 0) (γ 1)*(∫r in (s:ℝ)..(t:ℝ), G (geodesicExtension γ r))| := by
  have hrat : ∀ᵐ γ ∂π, ∀ q r : ℚ,
      dist (u (γ (rationalTime q))) (u (γ (rationalTime r))) ≤
        |dist (γ 0) (γ 1)*(∫t in (rationalTime q:ℝ)..(rationalTime r:ℝ), G (geodesicExtension γ t))| :=
    ae_all_iff.mpr (fun q => ae_all_iff.mpr (fun r =>
      hG.testPlan_ae_distance μ π hgeo hC hcomp hD _ _))
  have hrep : ∀ᵐ γ ∂π, ∀ q : ℚ, u (γ (rationalTime q)) = φ (γ (rationalTime q)) := by
    apply ae_all_iff.mpr
    intro q
    exact ae_of_ae_map (measurable_path_eval _).aemeasurable
      ((Measure.absolutelyContinuous_of_le_smul (hcomp _)).ae_eq hu)
  filter_upwards [hrat,hrep,testPlan_eval_intervalIntegrable μ π hC hcomp G] with γ hq he hi
  let v := fun r : ℝ => dist (γ 0) (γ 1)*G (geodesicExtension γ r)
  have hiv : IntervalIntegrable v volume 0 1 := hi.const_mul _
  have hac := hiv.absolutelyContinuousOnInterval_intervalIntegral
    (show (0:ℝ) ∈ uIcc 0 1 by simp)
  let J := fun t : Time => ∫r in (0:ℝ)..(t:ℝ), v r
  have hJ : Continuous J := by
    have hh := hac.continuousOn
    rw [uIcc_of_le zero_le_one,continuousOn_iff_continuous_domRestrict] at hh
    exact hh
  have hi0 (s : Time) : IntervalIntegrable v volume 0 (s:ℝ) := by
    apply hiv.mono_set
    rw [uIcc_of_le s.property.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl s.property.2
  have hJeq (s t : Time) : dist (J s) (J t) =
      |dist (γ 0) (γ 1)*(∫r in (s:ℝ)..(t:ℝ), G (geodesicExtension γ r))| := by
    rw [Real.dist_eq,abs_sub_comm]
    dsimp only [J]
    rw [intervalIntegral.integral_interval_sub_left (hi0 t) (hi0 s)]
    exact congrArg abs (intervalIntegral.integral_const_mul _ _)
  have hbound (s t : Time) : dist (φ (γ s)) (φ (γ t)) ≤ dist (J s) (J t) := by
    refine rationalTime_dense.induction_on₂
      (p := fun s t : Time => dist (φ (γ s)) (φ (γ t)) ≤ dist (J s) (J t)) ?_ ?_ s t
    · exact isClosed_le (((hφ.comp γ.continuous).comp continuous_fst).dist
        ((hφ.comp γ.continuous).comp continuous_snd))
        ((hJ.comp continuous_fst).dist (hJ.comp continuous_snd))
    · intro q r
      rw [hJeq]
      simpa only [he] using hq q r
  refine ⟨?_,fun s t => (hbound s t).trans_eq (hJeq s t)⟩
  apply absolutelyContinuous_of_dist_le hac
  intro s hs t ht
  rw [uIcc_of_le zero_le_one] at hs ht
  have hh := hbound ⟨s,hs⟩ ⟨t,ht⟩
  rw [← geodesicExtension_eq γ (⟨s,hs⟩:Time),← geodesicExtension_eq γ (⟨t,ht⟩:Time)] at hh
  exact hh

end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
 theorem abs_deriv_le_of_dist_domination {f P : ℝ → ℝ} {s f' p' : ℝ}
    (hf : HasDerivAt f f' s) (hP : HasDerivAt P p' s)
    (hbound : ∀ᶠ t in 𝓝 s, dist (f s) (f t) ≤ dist (P s) (P t)) :
    |f'| ≤ |p'| := by
  apply le_of_tendsto_of_tendsto (hasDerivAt_iff_tendsto_slope.mp hf).abs
    (hasDerivAt_iff_tendsto_slope.mp hP).abs
  filter_upwards [hbound.filter_mono nhdsWithin_le_nhds] with t ht
  simp only [Real.dist_eq] at ht
  rw [abs_sub_comm (f s),abs_sub_comm (P s)] at ht
  simpa only [slope_def_field,abs_div] using
    div_le_div_of_nonneg_right ht (abs_nonneg (t-s))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 theorem testPlan_eval_nonneg (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    {C : ℝ≥0∞} (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    {G : Lp ℝ 2 μ} (hG : 0 ≤ G) :
    ∀ᵐ γ ∂π, ∀ᵐ r ∂volume.restrict (Icc (0:ℝ) 1), 0 ≤ G (geodesicExtension γ r) := by
  have hac := Measure.absolutelyContinuous_of_le_smul (testPlanMeasure_compression μ π hcomp)
  have hnn := (Lp.coeFn_nonneg G).mpr hG
  have hh := ae_of_ae_map testPlanEval_measurable.aemeasurable (hnn.filter_mono hac.ae_le)
  exact Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hh)

 

 theorem IsRelaxedSlope.testPlan_ae_derivative (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G)
    {φ : X → ℝ} (hφ : Continuous φ) (hu : ⇑u =ᵐ[μ] φ) :
    ∀ᵐ γ ∂π, ∀ᵐ s : ℝ, s ∈ Ioo (0:ℝ) 1 →
      DifferentiableAt ℝ (fun r => φ (geodesicExtension γ r)) s ∧
      |deriv (fun r => φ (geodesicExtension γ r)) s| ≤
        dist (γ 0) (γ 1) * G (geodesicExtension γ s) := by
  filter_upwards [hG.testPlan_ae_absolutelyContinuous μ π hgeo hC hcomp hD hφ hu,
    testPlan_eval_intervalIntegrable μ π hC hcomp G,
    testPlan_eval_nonneg μ π hcomp (hG.nonneg μ)] with γ hγ hi hnon
  have hnon' : ∀ᵐ s : ℝ, s ∈ Icc (0:ℝ) 1 → 0 ≤ G (geodesicExtension γ s) :=
    (ae_restrict_iff' measurableSet_Icc).mp hnon
  let v := fun r : ℝ => dist (γ 0) (γ 1)*G (geodesicExtension γ r)
  have hiv : IntervalIntegrable v volume 0 1 := hi.const_mul _
  filter_upwards [hγ.1.ae_differentiableAt,hiv.ae_hasDerivAt_integral,hnon'] with s hd hp hn hs
  have hsc : s ∈ uIcc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using Ioo_subset_Icc_self hs
  have h0 : (0:ℝ) ∈ uIcc (0:ℝ) 1 := by simp
  refine ⟨hd hsc,?_⟩
  have hb : |deriv (fun r => φ (geodesicExtension γ r)) s| ≤ |v s| := by
    apply abs_deriv_le_of_dist_domination (hd hsc).hasDerivAt (hp hsc 0 h0)
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    have hst := hγ.2 (⟨s,Ioo_subset_Icc_self hs⟩:Time) (⟨t,Ioo_subset_Icc_self ht⟩:Time)
    rw [← geodesicExtension_eq γ (⟨s,Ioo_subset_Icc_self hs⟩:Time),
      ← geodesicExtension_eq γ (⟨t,Ioo_subset_Icc_self ht⟩:Time)] at hst
    have hi0 (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : IntervalIntegrable v volume 0 r := by
      apply hiv.mono_set
      rw [uIcc_of_le hr.1,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hr.2
    simp only [Real.dist_eq]
    rw [abs_sub_comm (φ (geodesicExtension γ s)),
      abs_sub_comm (∫ r in (0:ℝ)..s, v r),intervalIntegral.integral_interval_sub_left
      (hi0 t (Ioo_subset_Icc_self ht)) (hi0 s (Ioo_subset_Icc_self hs))]
    simpa only [Real.dist_eq,abs_sub_comm, v,intervalIntegral.integral_const_mul] using hst
  change _ ≤ |dist (γ 0) (γ 1)*G (geodesicExtension γ s)| at hb
  rwa [abs_of_nonneg (mul_nonneg dist_nonneg (hn (Ioo_subset_Icc_self hs)))] at hb
end

 
section
open Set Filter MeasureTheory
open scoped Topology

 

 theorem exists_continuous_extension_of_rat_control
    (f : ℚ → ℝ) (P : ℝ → ℝ) (hP : UniformContinuous P)
    (hbound : ∀ q r : ℚ, dist (f q) (f r) ≤ dist (P (q:ℝ)) (P (r:ℝ))) :
    ∃ F : ℝ → ℝ, UniformContinuous F ∧ (∀ q : ℚ, F (q:ℝ) = f q) ∧
      ∀ s t : ℝ, dist (F s) (F t) ≤ dist (P s) (P t) := by
  have hf : UniformContinuous f := by
    apply Metric.uniformContinuous_iff.mpr
    intro ε hε
    obtain ⟨δ,hδ,h⟩ := Metric.uniformContinuous_iff.mp
      (hP.comp Rat.uniformContinuous_coe_real) ε hε
    exact ⟨δ,hδ,fun {q r} hqr => (hbound q r).trans_lt (h hqr)⟩
  let e := Rat.isUniformEmbedding_coe_real.isUniformInducing
  let d := Rat.denseRange_cast (𝕜 := ℝ)
  let F := (e.isDenseInducing d).extend f
  have hF : UniformContinuous F := uniformContinuous_uniformly_extend e d hf
  have he (q : ℚ) : F (q:ℝ) = f q := uniformly_extend_of_ind e d hf q
  refine ⟨F,hF,he,?_⟩
  intro s t
  refine d.induction_on₂ (p := fun s t : ℝ => dist (F s) (F t) ≤ dist (P s) (P t)) ?_ ?_ s t
  · exact isClosed_le ((hF.continuous.comp continuous_fst).dist
        (hF.continuous.comp continuous_snd))
      ((hP.continuous.comp continuous_fst).dist (hP.continuous.comp continuous_snd))
  · intro q r
    simpa only [he] using hbound q r

end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace
noncomputable def testPlanPrimitive (μ : Measure X) (G : Lp ℝ 2 μ)
    (z : ℝ × C(Time,X)) : ℝ :=
  ∫r in (0:ℝ)..(Set.projIcc 0 1 zero_le_one z.1:ℝ), G (geodesicExtension z.2 r)

 theorem testPlanPrimitive_measurable (μ : Measure X) (G : Lp ℝ 2 μ) :
    Measurable (testPlanPrimitive μ G) := by
  let A : Set ((ℝ × C(Time,X)) × ℝ) :=
    {z | 0 < z.2 ∧ z.2 ≤ (Set.projIcc 0 1 zero_le_one z.1.1:ℝ)}
  have hp : Measurable (fun z : (ℝ × C(Time,X)) × ℝ =>
      (Set.projIcc 0 1 zero_le_one z.1.1:ℝ)) :=
    continuous_subtype_val.measurable.comp
      ((LipschitzWith.projIcc zero_le_one).continuous.measurable.comp
        (measurable_fst.comp measurable_fst))
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd hp)
  let f := fun z : (ℝ × C(Time,X)) × ℝ => G (geodesicExtension z.1.2 z.2)
  have hf : StronglyMeasurable f := (Lp.stronglyMeasurable G).comp_measurable
    (testPlanEval_measurable.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have h := (hf.indicator hA).integral_prod_right' (ν := volume)
  have he : (fun z : ℝ × C(Time,X) => ∫r : ℝ, A.indicator f (z,r)) = testPlanPrimitive μ G := by
    funext z
    rw [testPlanPrimitive,intervalIntegral.integral_of_le (Set.projIcc 0 1 zero_le_one z.1).property.1,
      ← integral_indicator measurableSet_Ioc]
    rfl
  rw [he] at h
  exact h.measurable

omit [BorelSpace X] in
 theorem testPlanPrimitive_uniformContinuous (μ : Measure X) (G : Lp ℝ 2 μ)
    (γ : C(Time,X)) (hi : IntervalIntegrable (fun r => G (geodesicExtension γ r)) volume 0 1) :
    UniformContinuous (fun t : ℝ => testPlanPrimitive μ G (t,γ)) := by
  have hh := (hi.absolutelyContinuousOnInterval_intervalIntegral
    (show (0:ℝ) ∈ uIcc 0 1 by simp)).continuousOn
  rw [uIcc_of_le zero_le_one,continuousOn_iff_continuous_domRestrict] at hh
  exact (CompactSpace.uniformContinuous_of_continuous hh).comp (LipschitzWith.projIcc zero_le_one).uniformContinuous

omit [BorelSpace X] in
 theorem testPlanPrimitive_dist (μ : Measure X) (G : Lp ℝ 2 μ)
    (γ : C(Time,X)) (hi : IntervalIntegrable (fun r => G (geodesicExtension γ r)) volume 0 1)
    (s t : ℝ) :
    dist (testPlanPrimitive μ G (s,γ)) (testPlanPrimitive μ G (t,γ)) =
      |∫r in (Set.projIcc 0 1 zero_le_one s:ℝ)..(Set.projIcc 0 1 zero_le_one t:ℝ),
        G (geodesicExtension γ r)| := by
  have hi0 (r : Time) : IntervalIntegrable (fun z => G (geodesicExtension γ z)) volume 0 (r:ℝ) := by
    apply hi.mono_set
    rw [uIcc_of_le r.property.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl r.property.2
  rw [Real.dist_eq,abs_sub_comm]
  exact congrArg abs (intervalIntegral.integral_interval_sub_left (hi0 _) (hi0 _))
noncomputable def testPlanClock (μ : Measure X) (G : Lp ℝ 2 μ)
    (z : ℝ × C(Time,X)) : ℝ :=
  dist (z.2 0) (z.2 1)*testPlanPrimitive μ G z

 theorem testPlanClock_measurable (μ : Measure X) (G : Lp ℝ 2 μ) :
    Measurable (testPlanClock μ G) :=
  ((((continuous_eval_const 0).dist (continuous_eval_const 1)).comp continuous_snd).measurable).mul
    (testPlanPrimitive_measurable μ G)

omit [BorelSpace X] in
 theorem testPlanClock_uniformContinuous (μ : Measure X) (G : Lp ℝ 2 μ)
    (γ : C(Time,X)) (hi : IntervalIntegrable (fun r => G (geodesicExtension γ r)) volume 0 1) :
    UniformContinuous (fun t : ℝ => testPlanClock μ G (t,γ)) :=
  (testPlanPrimitive_uniformContinuous μ G γ hi).const_mul' (dist (γ 0) (γ 1))

omit [BorelSpace X] in
 theorem testPlanClock_dist (μ : Measure X) (G : Lp ℝ 2 μ)
    (γ : C(Time,X)) (hi : IntervalIntegrable (fun r => G (geodesicExtension γ r)) volume 0 1)
    (s t : ℝ) :
    dist (testPlanClock μ G (s,γ)) (testPlanClock μ G (t,γ)) =
      |dist (γ 0) (γ 1)*(∫r in (Set.projIcc 0 1 zero_le_one s:ℝ)..
        (Set.projIcc 0 1 zero_le_one t:ℝ), G (geodesicExtension γ r))| := by
  unfold testPlanClock
  rw [Real.dist_eq,← mul_sub,abs_mul,← Real.dist_eq,testPlanPrimitive_dist μ G γ hi,
    ← abs_mul]
end

 
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 theorem IsRelaxedSlope.testPlan_ae_clock_rat (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) :
    ∀ᵐ γ ∂π, ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), ∀ q : ℚ,
      dist (u (geodesicExtension γ t)) (u (γ (rationalTime q))) ≤
        dist (testPlanClock μ G (t,γ)) (testPlanClock μ G ((q:ℝ),γ)) := by
  suffices hh : ∀ q : ℚ, ∀ᵐ γ ∂π, ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1),
      dist (u (geodesicExtension γ t)) (u (γ (rationalTime q))) ≤
        dist (testPlanClock μ G (t,γ)) (testPlanClock μ G ((q:ℝ),γ)) by
    filter_upwards [ae_all_iff.mpr hh] with γ hγ
    exact ae_all_iff.mpr hγ
  intro q
  have hm : MeasurableSet {z : ℝ × C(Time,X) |
      dist (u (testPlanEval z)) (u (z.2 (rationalTime q))) ≤
        dist (testPlanClock μ G z) (testPlanClock μ G ((q:ℝ),z.2))} := by
    apply measurableSet_le
    · exact ((Lp.stronglyMeasurable u).measurable.comp testPlanEval_measurable).dist
        ((Lp.stronglyMeasurable u).measurable.comp
          ((measurable_path_eval _).comp measurable_snd))
    · exact (testPlanClock_measurable μ G).dist ((testPlanClock_measurable μ G).comp
        (measurable_const.prodMk measurable_snd))
  have hh : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), ∀ᵐ γ ∂π,
      dist (u (geodesicExtension γ t)) (u (γ (rationalTime q))) ≤
        dist (testPlanClock μ G (t,γ)) (testPlanClock μ G ((q:ℝ),γ)) := by
    apply Eventually.of_forall
    intro t
    filter_upwards [hG.testPlan_ae_distance μ π hgeo hC hcomp hD
      (Set.projIcc 0 1 zero_le_one t) (rationalTime q),
      testPlan_eval_intervalIntegrable μ π hC hcomp G] with γ hγ hi
    rw [testPlanClock_dist μ G γ hi]
    exact hγ
  have hj := (Measure.ae_prod_iff_ae_ae hm).mpr hh
  exact Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hj)

 

 theorem IsRelaxedSlope.testPlan_ae_representative (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) :
    ∀ᵐ γ ∂π, ∃ F : ℝ → ℝ,
      AbsolutelyContinuousOnInterval F 0 1 ∧
      (∀ q : ℚ, F (q:ℝ) = u (γ (rationalTime q))) ∧
      (F =ᵐ[volume.restrict (Icc (0:ℝ) 1)] fun t => u (geodesicExtension γ t)) ∧
      ∀ s t : Time, dist (F s) (F t) ≤
        |dist (γ 0) (γ 1)*(∫r in (s:ℝ)..(t:ℝ), G (geodesicExtension γ r))| := by
  have hrat : ∀ᵐ γ ∂π, ∀ q r : ℚ,
      dist (u (γ (rationalTime q))) (u (γ (rationalTime r))) ≤
        |dist (γ 0) (γ 1)*(∫t in (rationalTime q:ℝ)..(rationalTime r:ℝ),
          G (geodesicExtension γ t))| :=
    ae_all_iff.mpr (fun q => ae_all_iff.mpr (fun r =>
      hG.testPlan_ae_distance μ π hgeo hC hcomp hD _ _))
  filter_upwards [hrat,testPlan_eval_intervalIntegrable μ π hC hcomp G,
    hG.testPlan_ae_clock_rat μ π hgeo hC hcomp hD] with γ hrat hi ha
  let P := fun t : ℝ => testPlanClock μ G (t,γ)
  have hP : UniformContinuous P := testPlanClock_uniformContinuous μ G γ hi
  obtain ⟨F,hF,he,hb⟩ := exists_continuous_extension_of_rat_control
    (fun q => u (γ (rationalTime q))) P hP (by
      intro q r
      rw [show dist (P (q:ℝ)) (P (r:ℝ)) = _ from testPlanClock_dist μ G γ hi _ _]
      exact hrat q r)
  have hFeq : F =ᵐ[volume.restrict (Icc (0:ℝ) 1)] fun t => u (geodesicExtension γ t) := by
    filter_upwards [ha] with t ht
    have hall (s : ℝ) : dist (u (geodesicExtension γ t)) (F s) ≤ dist (P t) (P s) := by
      refine (Rat.denseRange_cast (𝕜 := ℝ)).induction_on
        (p := fun s : ℝ => dist (u (geodesicExtension γ t)) (F s) ≤ dist (P t) (P s)) s ?_ ?_
      · exact isClosed_le (continuous_const.dist hF.continuous) (continuous_const.dist hP.continuous)
      · intro q
        rw [he]
        exact ht q
    have hh := hall t
    simpa using (dist_eq_zero.mp (le_antisymm (by simpa only [dist_self] using hh) dist_nonneg)).symm
  refine ⟨F,?_,he,hFeq,?_⟩
  · have hv : IntervalIntegrable (fun r => dist (γ 0) (γ 1)*G (geodesicExtension γ r)) volume 0 1 :=
      hi.const_mul _
    apply absolutelyContinuous_of_dist_le (hv.absolutelyContinuousOnInterval_intervalIntegral
      (show (0:ℝ) ∈ uIcc 0 1 by simp))
    intro s hs t ht
    rw [uIcc_of_le zero_le_one] at hs ht
    have hh := hb s t
    simpa only [P,testPlanClock,testPlanPrimitive,Set.projIcc_of_mem zero_le_one hs,
      Set.projIcc_of_mem zero_le_one ht,intervalIntegral.integral_const_mul] using hh
  · intro s t
    have hh := hb (s:ℝ) (t:ℝ)
    rw [show dist (P (s:ℝ)) (P (t:ℝ)) = _ from testPlanClock_dist μ G γ hi _ _] at hh
    simpa only [Set.projIcc_of_mem zero_le_one s.property,Set.projIcc_of_mem zero_le_one t.property] using hh

end RegularPointCoordinates

end OAI
