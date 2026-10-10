import Mathlib
import OAI.Analysis.RCDHeat.CompressionIntegral
import OAI.Analysis.RCDHeat.TestPlanContinuous

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: SobolevTestPlan, TestPlanStrongContinuity, TestPlanFlux, TestPlanInitialSlope. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology

 theorem ae_deriv_le_of_integral_domination {F v : ℝ → ℝ}
    (hF : AbsolutelyContinuousOnInterval F 0 1) (hv : IntervalIntegrable v volume 0 1)
    (hn : ∀ᵐ s : ℝ, s ∈ Icc (0:ℝ) 1 → 0 ≤ v s)
    (hb : ∀ s t : Time, dist (F s) (F t) ≤ |∫r in (s:ℝ)..(t:ℝ), v r|) :
    ∀ᵐ s : ℝ, s ∈ Ioo (0:ℝ) 1 → DifferentiableAt ℝ F s ∧ |deriv F s| ≤ v s := by
  filter_upwards [hF.ae_differentiableAt,hv.ae_hasDerivAt_integral,hn] with s hd hp hn hs
  have hsc : s ∈ uIcc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using Ioo_subset_Icc_self hs
  have h0 : (0:ℝ) ∈ uIcc (0:ℝ) 1 := by simp
  refine ⟨hd hsc,?_⟩
  have hh : |deriv F s| ≤ |v s| := by
    apply abs_deriv_le_of_dist_domination (hd hsc).hasDerivAt (hp hsc 0 h0)
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    have hh := hb (⟨s,Ioo_subset_Icc_self hs⟩:Time) (⟨t,Ioo_subset_Icc_self ht⟩:Time)
    have hi0 (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) : IntervalIntegrable v volume 0 r := by
      apply hv.mono_set
      rw [uIcc_of_le hr.1,uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hr.2
    rw [Real.dist_eq (∫r in (0:ℝ)..s,v r),abs_sub_comm,
      intervalIntegral.integral_interval_sub_left (hi0 t (Ioo_subset_Icc_self ht))
        (hi0 s (Ioo_subset_Icc_self hs))]
    exact hh
  rwa [abs_of_nonneg (hn (Ioo_subset_Icc_self hs))] at hh

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 theorem IsRelaxedSlope.testPlan_ae_weakDerivative (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) :
    ∀ᵐ γ ∂π, ∃ F : ℝ → ℝ,
      AbsolutelyContinuousOnInterval F 0 1 ∧ F 0 = u (γ 0) ∧ F 1 = u (γ 1) ∧
      (F =ᵐ[volume.restrict (Icc (0:ℝ) 1)] fun t => u (geodesicExtension γ t)) ∧
      (∀ s t : Time, dist (F s) (F t) ≤
        |dist (γ 0) (γ 1)*(∫r in (s:ℝ)..(t:ℝ), G (geodesicExtension γ r))|) ∧
      ∀ᵐ s : ℝ, s ∈ Ioo (0:ℝ) 1 → DifferentiableAt ℝ F s ∧
        |deriv F s| ≤ dist (γ 0) (γ 1)*G (geodesicExtension γ s) := by
  filter_upwards [hG.testPlan_ae_representative μ π hgeo hC hcomp hD,
    testPlan_eval_intervalIntegrable μ π hC hcomp G,
    testPlan_eval_nonneg μ π hcomp (hG.nonneg μ)] with γ hγ hi hn
  obtain ⟨F,hF,he,ha,hb⟩ := hγ
  refine ⟨F,hF,?_,?_,ha,hb,?_⟩
  · have hh := he 0
    simpa [rationalTime,Set.projIcc] using hh
  · have hh := he 1
    simpa [rationalTime,Set.projIcc] using hh
  · apply ae_deriv_le_of_integral_domination hF (hi.const_mul _)
    · have hh := (ae_restrict_iff' measurableSet_Icc).mp hn
      filter_upwards [hh] with s hs hsc
      exact mul_nonneg dist_nonneg (hs hsc)
    · intro s t
      simpa only [intervalIntegral.integral_const_mul] using hb s t

 

 theorem SobolevSpace.minimalSlope_testPlan (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    (u : SobolevSpace μ hQ) :
    ∀ᵐ γ ∂π, ∃ F : ℝ → ℝ,
      AbsolutelyContinuousOnInterval F 0 1 ∧
      F 0 = SobolevSpace.toLp μ hQ u (γ 0) ∧ F 1 = SobolevSpace.toLp μ hQ u (γ 1) ∧
      (F =ᵐ[volume.restrict (Icc (0:ℝ) 1)] fun t =>
        SobolevSpace.toLp μ hQ u (geodesicExtension γ t)) ∧
      (∀ s t : Time, dist (F s) (F t) ≤
        |dist (γ 0) (γ 1)*(∫r in (s:ℝ)..(t:ℝ),
          SobolevSpace.minimalSlope μ hQ u (geodesicExtension γ r))|) ∧
      ∀ᵐ s : ℝ, s ∈ Ioo (0:ℝ) 1 → DifferentiableAt ℝ F s ∧
        |deriv F s| ≤ dist (γ 0) (γ 1)*SobolevSpace.minimalSlope μ hQ u (geodesicExtension γ s) :=
  (SobolevSpace.minimalSlope_isRelaxed μ hQ u).testPlan_ae_weakDerivative μ π hgeo hC hcomp hD
end

 
section
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 theorem compressionPullback_norm_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (e : β → α) (he : Measurable e)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hcomp : ν.map e ≤ C • μ) :
    ‖compressionPullback μ ν e he hC hcomp‖ ≤ C.toReal ^ (1 / (2:ℝ≥0∞)).toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  intro f
  change ‖Lp.compMeasurePreserving e
    (show MeasurePreserving e ν (ν.map e) from ⟨he,rfl⟩) (Lp.LpToLpOfMeasureLeSMul hC hcomp f)‖ ≤ _
  rw [Lp.norm_compMeasurePreserving]
  exact (ContinuousLinearMap.le_opNorm _ f).trans
    (mul_le_mul_of_nonneg_right (Lp.norm_LpToLpOfMeasureLeSMul_le hC hcomp) (norm_nonneg f))

noncomputable def testPlanPullback (μ : Measure X) (π : Measure C(Time,X))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ) (t : Time) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 π :=
  compressionPullback μ π (fun γ => γ t) (measurable_path_eval t) hC (hcomp t)

 theorem testPlanPullback_toLp_ae (μ : Measure X) (π : Measure C(Time,X))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    {φ : X → ℝ} (hφ : MemLp φ 2 μ) (t : Time) :
    ⇑(testPlanPullback μ π hC hcomp t (hφ.toLp φ)) =ᵐ[π] fun γ => φ (γ t) := by
  refine (compressionPullback_ae μ π _ (measurable_path_eval t) hC (hcomp t) _).trans ?_
  exact ae_of_ae_map (measurable_path_eval t).aemeasurable
    ((Measure.absolutelyContinuous_of_le_smul (hcomp t)).ae_eq hφ.coeFn_toLp)

 theorem testPlanPullback_lipschitz (μ : Measure X) (π : Measure C(Time,X))
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hm : MemLp φ 2 μ) :
    LipschitzWith (L * ‖hD.toLp (fun γ : C(Time,X) => dist (γ 0) (γ 1))‖₊)
      (fun t : Time => testPlanPullback μ π hC hcomp t (hm.toLp φ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  let D : Lp ℝ 2 π := hD.toLp (fun γ : C(Time,X) => dist (γ 0) (γ 1))
  have hb : ‖testPlanPullback μ π hC hcomp s (hm.toLp φ) -
      testPlanPullback μ π hC hcomp t (hm.toLp φ)‖ ≤
      ‖((L:ℝ)*dist s t) • D‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (testPlanPullback μ π hC hcomp s (hm.toLp φ))
      (testPlanPullback μ π hC hcomp t (hm.toLp φ)),
      testPlanPullback_toLp_ae μ π hC hcomp hm s,
      testPlanPullback_toLp_ae μ π hC hcomp hm t,
      Lp.coeFn_smul ((L:ℝ)*dist s t) D,hD.coeFn_toLp,hgeo] with γ hsub hs ht hsm hDγ hγ
    change D γ = dist (γ 0) (γ 1) at hDγ
    simp only [hsub,Pi.sub_apply,hs,ht,hsm,Pi.smul_apply,hDγ,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg L.coe_nonneg,
      abs_of_nonneg dist_nonneg]
    have hh := hφ.dist_le_mul (γ s) (γ t)
    rw [hγ s t,Real.dist_eq] at hh
    simpa only [Subtype.dist_eq,Real.dist_eq,mul_assoc] using hh
  rw [dist_eq_norm]
  calc
    _ ≤ ‖((L:ℝ)*dist s t) • D‖ := hb
    _ = (↑(L * ‖D‖₊):ℝ)*dist s t := by
      rw [norm_smul,Real.norm_of_nonneg (mul_nonneg L.coe_nonneg dist_nonneg)]
      simp only [NNReal.coe_mul,coe_nnnorm]
      ring

 

 theorem lp_lipschitz_dense (μ : Measure X) [ProperSpace X] [μ.Regular] :
    Dense {u : Lp ℝ 2 μ | ∃ φ : X → ℝ, ∃ L : ℝ≥0, ∃ _hφ : LipschitzWith L φ,
      ∃ hm : MemLp φ 2 μ, hm.toLp φ = u} := by
  rw [Metric.dense_iff]
  intro u r hr
  obtain ⟨φ,happrox,⟨L,hL⟩,hm,_⟩ :=
    MemLp.exists_lipschitz_hasCompactSupport_eLpNorm_sub_le μ (Lp.memLp u)
      (ε := ENNReal.ofReal (r/2)) (by positivity)
  refine ⟨hm.toLp φ,?_,φ,L,hL,hm,rfl⟩
  rw [Metric.mem_ball,dist_comm,dist_eq_norm,Lp.norm_def]
  have hae : ⇑(u - hm.toLp φ) =ᵐ[μ] (fun x => u x - φ x) := by
    filter_upwards [Lp.coeFn_sub u (hm.toLp φ),hm.coeFn_toLp] with x hx hφ
    simp only [hx,Pi.sub_apply,hφ]
  rw [eLpNorm_congr_ae hae]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top happrox
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ r/2)] at hh
  exact hh.trans_lt (by linarith)

 

 theorem testPlanPullback_jointly_continuous (μ : Measure X)
    [ProperSpace X] [μ.Regular] (π : Measure C(Time,X))
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π) :
    Continuous (fun z : Lp ℝ 2 μ × Time => testPlanPullback μ π hC hcomp z.2 z.1) := by
  let M : ℝ≥0 := ⟨C.toReal ^ (1 / (2:ℝ≥0∞)).toReal,
    Real.rpow_nonneg ENNReal.toReal_nonneg _⟩
  apply continuous_prod_of_dense_continuous_lipschitzWith _ M (lp_lipschitz_dense μ)
  · rintro u ⟨φ,L,hφ,hm,rfl⟩
    exact (testPlanPullback_lipschitz μ π hgeo hC hcomp hD hφ hm).continuous
  · intro t
    apply (testPlanPullback μ π hC hcomp t).lipschitzWith.weaken
    change ‖testPlanPullback μ π hC hcomp t‖₊ ≤ M
    rw [← NNReal.coe_le_coe]
    exact compressionPullback_norm_le μ π _ (measurable_path_eval t) hC (hcomp t)


 
 theorem testPlanPullback_continuous (μ : Measure X)
    [ProperSpace X] [μ.Regular] (π : Measure C(Time,X))
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π) (u : Lp ℝ 2 μ) :
    Continuous (fun t : Time => testPlanPullback μ π hC hcomp t u) := by
  have hh : Continuous (fun z : Lp ℝ 2 μ × Time => testPlanPullback μ π hC hcomp z.2 z.1) :=
    testPlanPullback_jointly_continuous μ π hgeo hC hcomp hD
  have hp : Continuous (fun t : Time => (u,t)) := continuous_const.prodMk continuous_id
  change Continuous ((fun z : Lp ℝ 2 μ × Time => testPlanPullback μ π hC hcomp z.2 z.1) ∘
    (fun t : Time => (u,t)))
  exact Continuous.comp hh hp

 theorem testPlan_flux_continuous (μ : Measure X)
    [ProperSpace X] [μ.Regular] (π : Measure C(Time,X))
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π) (G : Lp ℝ 2 μ) :
    Continuous (fun t : ℝ => ∫γ : C(Time,X),
      dist (γ 0) (γ 1)*G (geodesicExtension γ t) ∂π) := by
  let D : Lp ℝ 2 π := hD.toLp (fun γ : C(Time,X) => dist (γ 0) (γ 1))
  have hp : Continuous (fun t : ℝ => testPlanPullback μ π hC hcomp
      (Set.projIcc 0 1 zero_le_one t) G) :=
    (testPlanPullback_continuous μ π hgeo hC hcomp hD G).comp
      (LipschitzWith.projIcc zero_le_one).continuous
  have hh : Continuous (fun t : ℝ => inner ℝ D
      (testPlanPullback μ π hC hcomp (Set.projIcc 0 1 zero_le_one t) G)) :=
    continuous_const.inner hp
  apply hh.congr
  intro t
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hD.coeFn_toLp,compressionPullback_ae μ π _
    (measurable_path_eval (Set.projIcc 0 1 zero_le_one t)) hC
    (hcomp (Set.projIcc 0 1 zero_le_one t)) G] with γ hDγ hGγ
  change D γ = dist (γ 0) (γ 1) at hDγ
  change (testPlanPullback μ π hC hcomp (Set.projIcc 0 1 zero_le_one t) G) γ =
    G (geodesicExtension γ t) at hGγ
  simp only [Real.inner_apply,hDγ,hGγ]

 

 theorem testPlan_flux_fubini (μ : Measure X) (π : Measure C(Time,X)) [IsFiniteMeasure π]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π) (G : Lp ℝ 2 μ)
    (t : Time) :
    Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)*
      (∫r in (0:ℝ)..(t:ℝ),G (geodesicExtension γ r))) π ∧
    (∫γ : C(Time,X), dist (γ 0) (γ 1)*
      (∫r in (0:ℝ)..(t:ℝ),G (geodesicExtension γ r)) ∂π) =
      ∫r in (0:ℝ)..(t:ℝ), (∫γ : C(Time,X),dist (γ 0) (γ 1)*G (geodesicExtension γ r) ∂π) := by
  have hi := (testPlan_length_memLp π hD).integrable_mul
    (testPlanMeasure_eval_memLp μ π hC hcomp G)
  have hit : Integrable (fun z : ℝ × C(Time,X) =>
      dist (z.2 0) (z.2 1)*G (geodesicExtension z.2 z.1))
      ((volume.restrict (Icc (0:ℝ) (t:ℝ))).prod π) := by
    apply hi.mono_measure
    apply Measure.prod_mono
    · exact Measure.restrict_mono (Icc_subset_Icc le_rfl t.2.2) le_rfl
    · exact le_rfl
  have he (γ : C(Time,X)) :
      dist (γ 0) (γ 1)*(∫r in (0:ℝ)..(t:ℝ),G (geodesicExtension γ r)) =
      ∫r in Icc (0:ℝ) (t:ℝ), dist (γ 0) (γ 1)*G (geodesicExtension γ r) := by
    rw [integral_const_mul,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le t.2.1]
  constructor
  · simpa only [he] using hit.integral_prod_right
  · simp_rw [he]
    rw [← integral_prod_symm _ hit,integral_prod _ hit,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le t.2.1]

end

 
open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

 theorem IsRelaxedSlope.testPlan_integrated_subinterval (μ : Measure X)
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) (t : Time) :
    (∫γ : C(Time,X), |u (γ t)-u (γ 0)| ∂π) ≤
      ∫r in (0:ℝ)..(t:ℝ), (∫γ : C(Time,X),dist (γ 0) (γ 1)*G (geodesicExtension γ r) ∂π) := by
  have hiu (s : Time) : MemLp (fun γ : C(Time,X) => u (γ s)) 2 π :=
    compressionPullback_memLp μ π _ (measurable_path_eval s) hC (hcomp s) u
  have hleft : Integrable (fun γ : C(Time,X) => |u (γ t)-u (γ 0)|) π :=
    ((hiu t).sub (hiu 0)).integrable (by norm_num) |>.abs
  obtain ⟨hri,he⟩ := testPlan_flux_fubini μ π hC hcomp hD G t
  rw [← he]
  exact integral_mono_ae hleft hri (hG.testPlan_ae_subinterval μ π hgeo hC hcomp hD 0 t t.2.1)

 

 theorem IsRelaxedSlope.testPlan_initial_bound (μ : Measure X)
    [ProperSpace X] [μ.Regular] (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝[>] (0:ℝ),
      (∫γ : C(Time,X), |u (geodesicExtension γ t)-u (γ 0)| ∂π)/t <
        (∫γ : C(Time,X),dist (γ 0) (γ 1)*G (γ 0) ∂π)+ε := by
  let F : ℝ → ℝ := fun t => ∫γ : C(Time,X),
    dist (γ 0) (γ 1)*G (geodesicExtension γ t) ∂π
  have hF : Continuous F := testPlan_flux_continuous μ π hgeo hC hcomp hD G
  have hd : HasDerivAt (fun t => ∫r in (0:ℝ)..t,F r) (F 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right (hF.intervalIntegrable 0 0)
      hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have ht : Tendsto (fun t => (∫r in (0:ℝ)..t,F r)/t) (𝓝[≠] (0:ℝ)) (𝓝 (F 0)) := by
    simpa only [slope_fun_def_field,intervalIntegral.integral_same,sub_zero] using hd.tendsto_slope
  have hfilt : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] (0:ℝ) :=
    nhdsWithin_mono 0 (fun t ht => (ne_of_gt ht : t ≠ 0))
  have hb : ∀ᶠ t in 𝓝[>] (0:ℝ), (∫r in (0:ℝ)..t,F r)/t < F 0+ε :=
    (ht.mono_left hfilt).eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
    (gt_mem_nhds (show (0:ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hb,hsmall,self_mem_nhdsWithin] with t ht ht1 ht0
  have h01 : t ∈ Icc (0:ℝ) 1 := ⟨le_of_lt ht0,le_of_lt ht1⟩
  have hi := hG.testPlan_integrated_subinterval μ π hgeo hC hcomp hD (⟨t,h01⟩:Time)
  have hge (γ : C(Time,X)) : geodesicExtension γ t = γ (⟨t,h01⟩:Time) :=
    geodesicExtension_eq γ (⟨t,h01⟩:Time)
  have hz : F 0 = ∫γ : C(Time,X), dist (γ 0) (γ 1)*G (γ 0) ∂π := by
    simp only [F,show ∀ γ : C(Time,X), geodesicExtension γ 0 = γ 0 from
      fun γ => geodesicExtension_eq γ 0]
  rw [← hz]
  calc
    _ = (∫γ : C(Time,X), |u (γ (⟨t,h01⟩:Time))-u (γ 0)| ∂π)/t := by simp_rw [hge]
    _ ≤ (∫r in (0:ℝ)..t,F r)/t := div_le_div_of_nonneg_right hi (le_of_lt ht0)
    _ < F 0+ε := ht


end RegularPointCoordinates

end OAI
