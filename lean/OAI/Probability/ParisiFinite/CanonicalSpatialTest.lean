import Mathlib
import OAI.Probability.ParisiFinite.HasDerivAtDeviation
import OAI.Probability.ParisiFinite.WeightedGradientField

namespace OAI

/-! Canonical Spatial Test. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath
variable {K M : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

def canonicalSpatialTest (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0}
    (hγ : Monotone γ) (hb : ∀ t,γ t≤β) (t : ℝ≥0) : QuadraticTest where
  val := field β γ t
  d1 := fieldGradient β γ t
  d2 := fieldCurvature β γ t
  hasD1 := hasDerivAt_field β hβ hγ hb t
  hasD2 := hasDerivAt_fieldGradient β hβ hγ hb t
  continuousD2 := (fieldCurvature_lipschitz β hβ hγ hb t).continuous
  c1 := 1
  c2 := β
  bound1 := fun x => fieldGradient_bound β hβ hγ hb t x
  bound2 := fun x => fieldCurvature_abs β hβ hγ hb t x

lemma finite_schedule_verification_at (hW : IsBrownianReal W P) (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (β : ℝ≥0) (hβ : 0<β) (ls : Schedule) (hw : width ls=1)
    (c : ℝ≥0) (hc0 : c≠0) (hc1 : c≤1) :
    (∫ ω,(finiteTimeField β hβ ls 0 c).val
      (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1⟩) ∂P)-recursion β ls 0=
      ∫ t in (0:ℝ)..(c:ℝ),∫ ω,finiteVerificationKernel β hβ ls b t
        (extend (solution b (brownianPath W ω)) t) ∂P := by
  let r := scheduleTimeRealization β hβ ls 0 le_rfl (by rw [hw];norm_num)
  have hh := brownian_solution_time_generator_at hW b r.test c hc0 hc1 hc
  have hsub : Ioc (0:ℝ) c⊆Ioc (0:ℝ) 1 := Ioc_subset_Ioc le_rfl (by exact_mod_cast hc1)
  have hr : volume.restrict (Ioc (0:ℝ) c)≤volume.restrict (Ioc (0:ℝ) 1) := Measure.restrict_mono_set _ hsub
  have hj : IntervalIntegrable (timeGeneratorC2 P W b r.test) volume 0 c := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le c.coe_nonneg]
    have hi := timeGeneratorC2_intervalIntegrable hW b r.test hc
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hi
    exact hi.mono_set hsub
  have ht : IntervalIntegrable (timeDerivativeC2 P W b r.test) volume 0 c := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le c.coe_nonneg]
    have hi := timeDerivativeC2_intervalIntegrable hW b r.test hc
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hi
    exact hi.mono_set hsub
  have h0 : r.test.val 0 0=recursion β ls 0 := by rw [r.val_eq,finiteTimeField_start]
  simp_rw [r.val_eq] at hh
  rw [finiteTimeField_start] at hh
  rw [hh,←intervalIntegral.integral_add hj ht]
  apply intervalIntegral.integral_congr_Ioo_of_le c.coe_nonneg
  intro t ht
  change (∫ ω,generatorC2 (r.test.slice t) b t (extend (solution b (brownianPath W ω)) t) ∂P)+
    (∫ ω,r.test.dt t (extend (solution b (brownianPath W ω)) t) ∂P)=_
  rw [←integral_add (generatorC2_integrable hW b _ t) (timeDerivativeC2_integrable_inner hW b r.test t)]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [generatorC2,TimeQuadraticTest.slice,r.d1_eq,r.d2_eq,r.dt_eq,finiteVerificationKernel]
  rw [finiteTimeField_PDE β hβ ls 0 t _ ht.1.le
    (by simpa only [hw,zero_add] using (ht.2.trans_le (show (c:ℝ)≤1 by exact_mod_cast hc1)))]
  ring

lemma expected_global_dyadic_field_tendsto (hW : IsBrownianReal W P)
    (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β)
    (b : Drift K M) (c : ℝ≥0) (hc : c<1) :
    Tendsto (fun n => ∫ ω,(finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 c).val
      (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩) ∂P) atTop
      (𝓝 (∫ ω,field β γ c (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩) ∂P)) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let X (ω : Ω) := solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc.le⟩
  have hx : Integrable X P := brownian_solution_integrable hW b _
  have hf : Integrable (fun ω => field β γ c (X ω)) P := (canonicalSpatialTest β hβ hγ hb c).integrable_comp hx
  apply tendsto_integral_of_dominated_convergence (fun ω => ‖field β γ c (X ω)‖+(β:ℝ))
    (fun n => ((finiteTimeField β hβ _ 0 c).lipschitz.continuous.measurable.comp_aemeasurable hx.aemeasurable).aestronglyMeasurable)
    (hf.norm.add (integrable_const _)) (fun n => ae_of_all _ fun ω => ?_)
    (ae_of_all _ fun ω => (global_dyadic_field_tendstoUniformly β hβ hγ hb c hc).tendsto_at (X ω))
  have he := global_dyadic_field_error β hβ hγ hb c hc n (X ω)
  have hm : (dyadicMesh 1 n:ℝ)≤1 := by
    exact_mod_cast dyadicMesh_le 1 n
  have hn := norm_le_norm_add_norm_sub (field β γ c (X ω)) ((finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 c).val (X ω))
  simp only [Real.norm_eq_abs] at hn
  rw [abs_sub_comm (field β γ c (X ω))] at hn
  have ht := mul_le_mul_of_nonneg_left hm β.coe_nonneg
  simp only [Function.comp_apply,Real.norm_eq_abs]
  linarith

theorem canonical_verification_at (hW : IsBrownianReal W P) (b : Drift K M)
    (hc : ∀ᵐ t ∂volume,t∈Icc (0:ℝ) 1 → ∀ x,ContinuousAt (uncurry b.val) (t,x))
    (β : ℝ≥0) (hβ : 0<β) {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (hb : ∀ t,γ t≤β)
    (c : ℝ≥0) (hc0 : c≠0) (hc1 : c<1) :
    (∫ ω,field β γ c
      (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1.le⟩) ∂P)-
      field β γ 0 0=
        ∫ t in (0:ℝ)..(c:ℝ),∫ ω,verificationKernel β γ b t
          (extend (solution b (brownianPath W ω)) t) ∂P := by
  have hsub : Ioc (0:ℝ) c⊆Ioc (0:ℝ) 1 := Ioc_subset_Ioc le_rfl (by exact_mod_cast hc1.le)
  have hi : Tendsto (fun n => ∫ t in (0:ℝ)..(c:ℝ),∫ ω,
      finiteVerificationKernel β hβ (dyadicSchedule γ false 0 1 n) b t
        (extend (solution b (brownianPath W ω)) t) ∂P) atTop
      (𝓝 (∫ t in (0:ℝ)..(c:ℝ),∫ ω,verificationKernel β γ b t
        (extend (solution b (brownianPath W ω)) t) ∂P)) := by
    have hmeas (n : ℕ) : AEStronglyMeasurable
        (fun t => ∫ ω,finiteVerificationKernel β hβ (dyadicSchedule γ false 0 1 n) b t
          (extend (solution b (brownianPath W ω)) t) ∂P) (volume.restrict (uIoc (0:ℝ) c)) := by
      rw [uIoc_of_le c.coe_nonneg]
      exact (expected_finiteVerificationKernel_aestronglyMeasurable hW β hβ _
        (by simpa only [NNReal.coe_one] using dyadicSchedule_width γ false 0 1 n) b hc).mono_measure
          (Measure.restrict_mono_set _ hsub)
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (M:ℝ)+(β:ℝ)/2) (Eventually.of_forall hmeas)
      (Eventually.of_forall fun n => ae_of_all _ fun t _ =>
        expected_finiteVerificationKernel_bound hW β hβ _ (dyadicSchedule_coeff_bound hb false 0 1 n) b t)
      intervalIntegrable_const
    filter_upwards [global_dyadic_coefficient_tendsto_ae hγ] with t ht hmem
    rw [uIoc_of_le c.coe_nonneg] at hmem
    have hti : t∈Ioo (0:ℝ) 1 := ⟨hmem.1,hmem.2.trans_lt (by exact_mod_cast hc1)⟩
    exact expected_global_dyadic_verificationKernel_tendsto hW β hβ hγ hb b t hti (ht hti)
  have h0 : Tendsto (fun n => recursion β (dyadicSchedule γ false 0 1 n) 0) atTop (𝓝 (field β γ 0 0)) := by
    have hh := (global_dyadic_field_tendstoUniformly β hβ hγ hb 0 (by norm_num)).tendsto_at 0
    simpa only [NNReal.coe_zero,finiteTimeField_start] using hh
  have he : (fun n => (∫ ω,(finiteTimeField β hβ (dyadicSchedule γ false 0 1 n) 0 c).val
      (solution b (brownianPath W ω) ⟨c,c.coe_nonneg,by exact_mod_cast hc1.le⟩) ∂P)-
      recursion β (dyadicSchedule γ false 0 1 n) 0)=
    (fun n => ∫ t in (0:ℝ)..(c:ℝ),∫ ω,finiteVerificationKernel β hβ (dyadicSchedule γ false 0 1 n) b t
      (extend (solution b (brownianPath W ω)) t) ∂P) := by
    funext n
    exact finite_schedule_verification_at hW b hc β hβ _
      (by simpa only [NNReal.coe_one] using dyadicSchedule_width γ false 0 1 n) c hc0 hc1.le
  exact tendsto_nhds_unique
    ((expected_global_dyadic_field_tendsto hW β hβ hγ hb b c hc1).sub h0) (he ▸ hi)

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite
open ParisiPath BoundedCoefficient
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {β : ℝ≥0}

lemma minimizingParisi_potential_average_eq (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {q : OrderPoint} (hq : q∈(ρ:Measure OrderPoint).support) :
    (∫ x,variationalPotential P W hβ (ofMeasure β ρ) x ∂(ρ:Measure OrderPoint))=
      variationalPotential P W hβ (ofMeasure β ρ) q := by
  calc
    _ = ∫ _ : OrderPoint,variationalPotential P W hβ (ofMeasure β ρ) q ∂(ρ:Measure OrderPoint) := by
      apply integral_congr_ae
      filter_upwards [(ρ:Measure OrderPoint).support_mem_ae] with x hx
      exact le_antisymm (minimizingParisi_support_potential hW hβ hρ hx q)
        (minimizingParisi_support_potential hW hβ hρ hq x)
    _ = _ := by simp

lemma ofMeasure_real_after_support (ρ : ProbabilityMeasure OrderPoint) (β : ℝ≥0)
    (q : OrderPoint) (hq : ∀ t∈(ρ:Measure OrderPoint).support,t≤q)
    (r : ℝ) (hr : (q:ℝ)≤r) : (ofMeasure β ρ).real r=β := by
  change (measureCoefficient ρ β (Real.toNNReal r):ℝ)=β
  rw [measureCoefficient_after_support ρ β q hq]
  rw [Real.coe_toNNReal r (q.property.1.trans hr)]
  exact hr

lemma minimizingParisi_weighted_deviation (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {q : OrderPoint} (hq : q∈(ρ:Measure OrderPoint).support)
    (hqmax : ∀ t∈(ρ:Measure OrderPoint).support,t≤q) :
    (∫ t in (0:ℝ)..(q:ℝ),(ofMeasure β ρ).real t*deviation P W hβ (ofMeasure β ρ) t)=0 := by
  let c := ofMeasure β ρ
  have hd := continuous_deviation hW hβ c
  have hit (a b : ℝ) : IntervalIntegrable (fun t => c.real t*deviation P W hβ c t) volume a b :=
    (c.real_intervalIntegrable a b).mul_continuousOn hd.continuousOn
  have hall : (∫ t in (0:ℝ)..1,c.real t*deviation P W hβ c t)=
      (β:ℝ)*variationalPotential P W hβ c q := by
    calc
      _ = (β:ℝ)*(∫ t in (0:ℝ)..1,(ρ:Measure OrderPoint).real {x | (x:ℝ)≤t}*deviation P W hβ c t) := by
        rw [←intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        dsimp only [c]
        rw [ofMeasure_real β ρ t ht.1]
        ring
      _ = (β:ℝ)*(∫ x,variationalPotential P W hβ c x ∂(ρ:Measure OrderPoint)) := by
        rw [integral_cdf_mul ρ hd (by norm_num) (norm_deviation_le hW hβ c)]
        rfl
      _ = _ := by rw [minimizingParisi_potential_average_eq hW hβ hρ hq]
  have htail : (∫ t in (q:ℝ)..1,c.real t*deviation P W hβ c t)=
      (β:ℝ)*variationalPotential P W hβ c q := by
    rw [variationalPotential,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le q.property.2] at ht
    dsimp only
    rw [show c.real t=(β:ℝ) from ofMeasure_real_after_support ρ β q hqmax t ht.1]
  have he := intervalIntegral.integral_add_adjacent_intervals (hit 0 q) (hit q 1)
  rw [hall,htail] at he
  exact add_right_cancel (he.trans (zero_add _).symm)

lemma minimizingParisi_weighted_consistency (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {q : OrderPoint} (hq : q∈(ρ:Measure OrderPoint).support)
    (hqmax : ∀ t∈(ρ:Measure OrderPoint).support,t≤q) :
    (∫ t in (0:ℝ)..(q:ℝ),(ofMeasure β ρ).real t*
      expectedProduct P W (ofMeasure β ρ) (ofMeasure β ρ) ((ofMeasure β ρ).driftData hβ) t)=
      ∫ t in (0:ℝ)..(q:ℝ),t*(ofMeasure β ρ).real t := by
  let c := ofMeasure β ρ
  have hi : IntervalIntegrable (fun t => c.real t*expectedProduct P W c c (c.driftData hβ) t) volume 0 q :=
    (c.real_intervalIntegrable 0 q).mul_continuousOn (expectedProduct_continuous hW c c hβ _).continuousOn
  have hj : IntervalIntegrable (fun t => t*c.real t) volume 0 q :=
    (c.real_intervalIntegrable 0 q).continuousOn_mul continuous_id.continuousOn
  apply sub_eq_zero.mp
  rw [←intervalIntegral.integral_sub hi hj]
  convert minimizingParisi_weighted_deviation hW hβ hρ hq hqmax using 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only [deviation,c]
  ring

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath
namespace BoundedCoefficient
variable {β : ℝ≥0}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
variable {K M : ℝ≥0}

lemma curvature_integrable (hW : IsBrownianReal W P) (c : BoundedCoefficient β)
    (hβ : 0<β) (b : Drift K M) (t : ℝ) :
    Integrable (fun ω => c.curvature (solution b (brownianPath W ω)) t) P := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact Integrable.of_bound (c.curvature_aestronglyMeasurable hW hβ b t) (β:ℝ)
    (ae_of_all _ fun ω => c.norm_curvature_le hβ _ t)

def expectedCurvature (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (c : BoundedCoefficient β) (hβ : 0<β) (t : ℝ) : ℝ :=
  ∫ ω,c.curvature (solution (c.driftData hβ) (brownianPath W ω)) t ∂P

lemma expectedCurvature_continuous (hW : IsBrownianReal W P)
    (c : BoundedCoefficient β) (hβ : 0<β) : Continuous (c.expectedCurvature P W hβ) := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact continuous_of_dominated (bound := fun _ => (β:ℝ))
    (fun t => (curvature_integrable hW c hβ _ t).aestronglyMeasurable)
    (fun t => ae_of_all _ fun ω => c.norm_curvature_le hβ _ t) (integrable_const _)
    (ae_of_all _ fun ω => c.continuous_curvature hβ _)

lemma expectedCurvature_nonneg (c : BoundedCoefficient β) (hβ : 0<β) (t : ℝ) :
    0≤c.expectedCurvature P W hβ t := integral_nonneg fun _ => (c.curvature_pos hβ _ t).le

lemma expectedCurvature_bound (hW : IsBrownianReal W P)
    (c : BoundedCoefficient β) (hβ : 0<β) (t : ℝ) : ‖c.expectedCurvature P W hβ t‖≤β := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (norm_integral_le_of_norm_le_const (μ:=P) (ae_of_all _ fun ω => c.norm_curvature_le hβ _ t)).trans_eq (by simp)

lemma position_spin (hW : IsBrownianReal W P) (c : BoundedCoefficient β) (hβ : 0<β)
    (q : OrderPoint) (hq0 : 0<(q:ℝ)) (hq1 : (q:ℝ)<1) :
    (∫ ω,(solution (c.driftData hβ) (brownianPath W ω) q)*
      c.spin (solution (c.driftData hβ) (brownianPath W ω)) q ∂P)=
      (∫ t in (0:ℝ)..(q:ℝ),c.expectedCurvature P W hβ t)+
      ∫ t in (0:ℝ)..(q:ℝ),c.real t*expectedProduct P W c c (c.driftData hβ) t := by
  let r : ℝ≥0 := ⟨q,q.property.1⟩
  have hr0 : r≠0 := ne_of_gt (show 0<r from hq0)
  have hr1 : r<1 := by exact_mod_cast hq1
  have hh := c.position_spin_raw hW hβ r hr0 hr1
  have hleft : (∫ ω,(solution (c.driftData hβ) (brownianPath W ω) ⟨r,r.coe_nonneg,by exact_mod_cast hr1.le⟩)*
      fieldGradient β c.val r (solution (c.driftData hβ) (brownianPath W ω) ⟨r,r.coe_nonneg,by exact_mod_cast hr1.le⟩) ∂P)=
      ∫ ω,(solution (c.driftData hβ) (brownianPath W ω) q)*c.spin (solution (c.driftData hβ) (brownianPath W ω)) q ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [spin_eq _ _ _ q.property,extend_of_mem _ q.property]
    rw [show Real.toNNReal (q:ℝ)=r from by
      apply NNReal.coe_injective
      exact Real.coe_toNNReal _ q.property.1]
    rfl
  rw [hleft] at hh
  rw [hh]
  dsimp only [r]
  have hi := (c.expectedCurvature_continuous hW hβ).intervalIntegrable (μ:=volume) 0 (q:ℝ)
  have hj : IntervalIntegrable (fun t => c.real t*expectedProduct P W c c (c.driftData hβ) t) volume 0 q :=
    (c.real_intervalIntegrable 0 q).mul_continuousOn (expectedProduct_continuous hW c c hβ _).continuousOn
  rw [←intervalIntegral.integral_add hi hj]
  apply intervalIntegral.integral_congr
  intro t ht
  change t∈uIcc (0:ℝ) (q:ℝ) at ht
  rw [uIcc_of_le q.property.1] at ht
  have ht' : t∈Icc (0:ℝ) 1 := ⟨ht.1,ht.2.trans q.property.2⟩
  change (∫ ω,fieldCurvature β c.val (Real.toNNReal t) _+c.real t*(fieldGradient β c.val (Real.toNNReal t) _)^2 ∂P)=_
  dsimp only
  rw [expectedCurvature,expectedProduct,←integral_const_mul,←integral_add
    (c.curvature_integrable hW hβ _ t) ((c.spin_product_integrable hW c hβ _ t).const_mul _)]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [curvature_eq _ _ _ ht',spin_eq _ _ _ ht']
  ring

lemma field_value_at (hW : IsBrownianReal W P) (c : BoundedCoefficient β) (hβ : 0<β)
    (q : OrderPoint) (hq0 : 0<(q:ℝ)) (hq1 : (q:ℝ)<1) :
    (∫ ω,field β c.val ⟨q,q.property.1⟩ (solution (c.driftData hβ) (brownianPath W ω) q) ∂P)=
      field β c.val 0 0+(∫ t in (0:ℝ)..(q:ℝ),c.real t*expectedProduct P W c c (c.driftData hβ) t)/2 := by
  let r : ℝ≥0 := ⟨q,q.property.1⟩
  have hr0 : r≠0 := ne_of_gt (show 0<r from hq0)
  have hr1 : r<1 := by exact_mod_cast hq1
  have hh := canonical_verification_at hW (c.driftData hβ) (c.drift_joint_ae_continuous hβ)
    β hβ c.mono c.bound r hr0 hr1
  have he : (∫ t in (0:ℝ)..(r:ℝ),∫ ω,verificationKernel β c.val (c.driftData hβ) t
      (extend (solution (c.driftData hβ) (brownianPath W ω)) t) ∂P)=
      (∫ t in (0:ℝ)..(q:ℝ),c.real t*expectedProduct P W c c (c.driftData hβ) t)/2 := by
    rw [←intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t ht
    change t∈uIcc (0:ℝ) (q:ℝ) at ht
    rw [uIcc_of_le q.property.1] at ht
    dsimp only
    rw [expected_verificationKernel_eq_feedback hW c c hβ t ⟨ht.1,ht.2.trans q.property.2⟩]
    dsimp only [feedbackKernel]
    ring
  rw [he] at hh
  exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)

end BoundedCoefficient
open BoundedCoefficient
variable {β : ℝ≥0}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma minimizingParisi_position_spin (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {q : OrderPoint} (hq : q∈(ρ:Measure OrderPoint).support)
    (hqmax : ∀ t∈(ρ:Measure OrderPoint).support,t≤q) (hq0 : 0<(q:ℝ)) (hq1 : (q:ℝ)<1) :
    (∫ ω,(solution ((ofMeasure β ρ).driftData hβ) (brownianPath W ω) q)*
      (ofMeasure β ρ).spin (solution ((ofMeasure β ρ).driftData hβ) (brownianPath W ω)) q ∂P)=
      (∫ t in (0:ℝ)..(q:ℝ),(ofMeasure β ρ).expectedCurvature P W hβ t)+
      ∫ t in (0:ℝ)..(q:ℝ),t*(ofMeasure β ρ).real t := by
  rw [(ofMeasure β ρ).position_spin hW hβ q hq0 hq1,
    minimizingParisi_weighted_consistency hW hβ hρ hq hqmax]

lemma minimizingParisi_field_value_at (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {q : OrderPoint} (hq : q∈(ρ:Measure OrderPoint).support)
    (hqmax : ∀ t∈(ρ:Measure OrderPoint).support,t≤q) (hq0 : 0<(q:ℝ)) (hq1 : (q:ℝ)<1) :
    (∫ ω,field β (measureCoefficient ρ β) ⟨q,q.property.1⟩
      (solution ((ofMeasure β ρ).driftData hβ) (brownianPath W ω) q) ∂P)=
      field β (measureCoefficient ρ β) 0 0+(∫ t in (0:ℝ)..(q:ℝ),t*(ofMeasure β ρ).real t)/2 := by
  have hh := (ofMeasure β ρ).field_value_at hW hβ q hq0 hq1
  rw [minimizingParisi_weighted_consistency hW hβ hρ hq hqmax] at hh
  exact hh

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite

lemma terminal_entropy_loss {β : ℝ} (hβ : 0<β) (x : ℝ) :
    terminal β x-Real.log 2/β≤x*Real.tanh (β*x) := by
  let g (x : ℝ) := x*Real.tanh (β*x)-terminal β x
  have hd (x : ℝ) : HasDerivAt g (x*(β/(Real.cosh (β*x))^2)) x := by
    convert ((hasDerivAt_id x).mul (hasDerivAt_tanh_scaled β x)).sub (hasDerivAt_terminal hβ x) using 1 <;> first | rfl | (dsimp only [g,id_eq];ring)
  have hm : MonotoneOn g (Ici (0:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hd x).deriv]
    have hx' : 0≤x := interior_subset hx
    positivity
  have he (x : ℝ) : g (-x)=g x := by
    dsimp only [g,terminal]
    rw [mul_neg,Real.tanh_neg,Real.cosh_neg,neg_mul_neg]
  have hz : g 0= -(Real.log 2/β) := by simp [g]
  have hg : g 0≤g x := by
    by_cases hx : 0≤x
    · exact hm (by simp) hx hx
    · have hh := hm (by simp) (show -x∈Ici (0:ℝ) by simp;linarith) (by linarith : (0:ℝ)≤ -x)
      simpa only [he] using hh
  rw [hz] at hg
  dsimp only [g] at hg
  linarith

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal
namespace ParisiFinite
open ParisiPath BoundedCoefficient
variable {β : ℝ≥0}

lemma measureFunctional_eq_field_penalty (ρ : ProbabilityMeasure OrderPoint) :
    measureFunctional β ρ=field β (measureCoefficient ρ β) 0 0-
      (∫ t in (0:ℝ)..1,t*(ofMeasure β ρ).real t)/2 := by
  simp only [measureFunctional,orderParameterFunctional,field,tsub_zero,
    coefficientPenalty,zero_add,NNReal.coe_zero,NNReal.coe_one,
    intervalIntegral.integral_div,BoundedCoefficient.real,ofMeasure]

lemma minimizingParisi_value_eq_pressure (hβ : 0<β) {ρ : ProbabilityMeasure OrderPoint}
    (hρ : IsMinimizingParisiMeasure β ρ) : measureFunctional β ρ=SKQAOA.limitingFreeEnergy β := by
  obtain ⟨ν,hν,he⟩ := exists_minimizing_Parisi_measure hβ
  exact le_antisymm ((hρ ν).trans_eq he) (pressure_le_measureFunctional hβ ρ)

lemma measureCoefficient_penalty_split (ρ : ProbabilityMeasure OrderPoint)
    (q : OrderPoint) (hqmax : ∀ t∈(ρ:Measure OrderPoint).support,t≤q) :
    (∫ t in (0:ℝ)..1,t*(ofMeasure β ρ).real t)=
      (∫ t in (0:ℝ)..(q:ℝ),t*(ofMeasure β ρ).real t)+(β:ℝ)*(1-(q:ℝ)^2)/2 := by
  let c := ofMeasure β ρ
  have hi (a b : ℝ) : IntervalIntegrable (fun t => t*c.real t) volume a b :=
    (c.real_intervalIntegrable a b).continuousOn_mul continuous_id.continuousOn
  rw [←intervalIntegral.integral_add_adjacent_intervals (hi 0 q) (hi q 1)]
  congr 1
  calc
    _ = ∫ t in (q:ℝ)..1,t*(β:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le q.property.2] at ht
      dsimp only
      rw [ofMeasure_real_after_support ρ β q hqmax t ht.1]
    _ = _ := by rw [intervalIntegral.integral_mul_const,integral_id];ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

lemma minimizingParisi_value_at_endpoint_raw (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {q : OrderPoint} (hq : q∈(ρ:Measure OrderPoint).support)
    (hqmax : ∀ t∈(ρ:Measure OrderPoint).support,t≤q) (hq0 : 0<(q:ℝ)) (hq1 : (q:ℝ)<1) :
    SKQAOA.limitingFreeEnergy β-(β:ℝ)*(1-(q:ℝ))^2/4-Real.log 2/(β:ℝ)≤
      ∫ t in (0:ℝ)..(q:ℝ),(ofMeasure β ρ).expectedCurvature P W hβ t := by
  let : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let c := ofMeasure β ρ
  let X (ω : Ω) := solution (c.driftData hβ) (brownianPath W ω)
  let r : ℝ≥0 := ⟨q,q.property.1⟩
  have hr : r≤1 := by exact_mod_cast q.property.2
  have hp : ∀ s : ℝ≥0,r ≤ s → c.val s=β := by
    intro s hs
    exact measureCoefficient_after_support ρ β q hqmax s (NNReal.coe_le_coe.mpr hs)
  have hsm (ω : Ω) : c.spin (X ω) q=fieldGradient β c.val r (X ω q) := by
    rw [spin_eq _ _ _ q.property,extend_of_mem _ q.property]
    congr 1
    apply NNReal.coe_injective
    exact Real.coe_toNNReal _ q.property.1
  have hh (ω : Ω) : field β c.val r (X ω q)-(β:ℝ)*(1-(q:ℝ))/2-Real.log 2/(β:ℝ)≤
      (X ω q)*c.spin (X ω) q := by
    rw [hsm,field_final_plateau β hβ r hr hp,fieldGradient_final_plateau β hβ r hr hp]
    change terminal β (X ω q)+(β:ℝ)*(1-(q:ℝ))/2-
      (β:ℝ)*(1-(q:ℝ))/2-Real.log 2/(β:ℝ)≤(X ω q)*Real.tanh ((β:ℝ)*(X ω q))
    linarith [terminal_entropy_loss (show (0:ℝ)<β from hβ) (X ω q)]
  have hx : Integrable (fun ω => X ω q) P := brownian_solution_integrable hW _ q
  have hf : Integrable (fun ω => field β c.val r (X ω q)) P :=
    (canonicalSpatialTest β hβ c.mono c.bound r).integrable_comp hx
  have hm : Integrable (fun ω => (X ω q)*c.spin (X ω) q) P := hx.mul_bdd
    (c.spin_aestronglyMeasurable hW hβ _ q) (ae_of_all _ fun ω => c.norm_spin_le hβ (X ω) q)
  have hle := integral_mono ((hf.sub (integrable_const _)).sub (integrable_const _)) hm hh
  dsimp only [Pi.sub_apply] at hle
  have hsplit := integral_sub (hf.sub (integrable_const ((β:ℝ)*(1-(q:ℝ))/2)))
    (integrable_const (Real.log 2/(β:ℝ)))
  dsimp only [Pi.sub_apply] at hsplit
  rw [hsplit,integral_sub hf (integrable_const _)] at hle
  simp only [integral_const,probReal_univ,one_smul] at hle
  have hpos := minimizingParisi_position_spin hW hβ hρ hq hqmax hq0 hq1
  have hfield := minimizingParisi_field_value_at hW hβ hρ hq hqmax hq0 hq1
  change (∫ ω,field β (measureCoefficient ρ β) ⟨q,q.property.1⟩
    (solution ((ofMeasure β ρ).driftData hβ) (brownianPath W ω) q) ∂P)-
      (β:ℝ)*(1-(q:ℝ))/2-Real.log 2/(β:ℝ)≤
        (∫ ω,(solution ((ofMeasure β ρ).driftData hβ) (brownianPath W ω) q)*
          (ofMeasure β ρ).spin (solution ((ofMeasure β ρ).driftData hβ) (brownianPath W ω)) q ∂P) at hle
  rw [hpos,hfield] at hle
  have hval := measureFunctional_eq_field_penalty (β:=β) ρ
  rw [minimizingParisi_value_eq_pressure hβ hρ,measureCoefficient_penalty_split ρ q hqmax] at hval
  nlinarith

 

theorem minimizingParisi_value_at_endpoint (hW : IsBrownianReal W P) (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ)
    {q : OrderPoint} (hq : q∈(ρ:Measure OrderPoint).support)
    (hqmax : ∀ t∈(ρ:Measure OrderPoint).support,t≤q) (hq0 : 0<(q:ℝ)) (hq1 : (q:ℝ)<1) :
    SKQAOA.Pstar-(1/4+Real.log 2)/(β:ℝ)≤
      ∫ t in (0:ℝ)..(q:ℝ),(ofMeasure β ρ).expectedCurvature P W hβ t := by
  have hb : (0:ℝ)<β := hβ
  have hqbd := minimizingParisi_endpoint_bound hW hβ hρ hq hqmax hq0 hq1
  have hsmall : (β:ℝ)*(1-(q:ℝ))^2/4≤(1/4)/(β:ℝ) := by
    calc
      _ ≤ (β:ℝ)*(1/(β:ℝ))^2/4 := by gcongr
      _ = _ := by field_simp
  have hv := minimizingParisi_value_at_endpoint_raw hW hβ hρ hq hqmax hq0 hq1
  have hf := (SKQAOA.limitingFreeEnergy_bounds hb).1
  have he : (1/4+Real.log 2)/(β:ℝ)=(1/4)/(β:ℝ)+Real.log 2/(β:ℝ) := add_div _ _ _
  rw [he]
  linarith

end ParisiFinite

 

 

 

open MeasureTheory ProbabilityTheory Filter Function Set
open scoped Topology NNReal ENNReal
namespace ParisiFinite
open ParisiPath BoundedCoefficient BrownianConstruction

 

theorem minimizingParisi_zero_in_support {β : ℝ≥0} (hβ : 0<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ) :
    (⟨0,by simp⟩ : OrderPoint)∈(ρ:Measure OrderPoint).support :=
  minimizingParisi_zero_mem_support brownianMotion_isBrownian hβ hρ

 

theorem minimizingParisi_support_boundary {β : ℝ≥0} (hβ : (1:ℝ)<β)
    {ρ : ProbabilityMeasure OrderPoint} (hρ : IsMinimizingParisiMeasure β ρ) :
    ∃ q : OrderPoint, 0<(q:ℝ) ∧ (q:ℝ)<1 ∧
      q∈(ρ:Measure OrderPoint).support ∧
      (∀ t∈(ρ:Measure OrderPoint).support,t≤q) ∧ 1-(q:ℝ)≤1/(β:ℝ) := by
  have hbp : 0<β := by exact_mod_cast (zero_lt_one.trans hβ)
  obtain ⟨q,hq0,hq1,hq,hqmax⟩ :=
    minimizingParisi_support_endpoint brownianMotion_isBrownian hβ hρ
  exact ⟨q,hq0,hq1,hq,hqmax,
    minimizingParisi_endpoint_bound brownianMotion_isBrownian hbp hρ hq hqmax hq0 hq1⟩

 

theorem exists_minimizingParisi_endpoint_value {β : ℝ≥0} (hβ : (1:ℝ)<β) :
    ∃ (ρ : ProbabilityMeasure OrderPoint) (q : OrderPoint) (hbp : 0<β),
      IsMinimizingParisiMeasure β ρ ∧
      measureFunctional β ρ=SKQAOA.limitingFreeEnergy β ∧
      (⟨0,by simp⟩ : OrderPoint)∈(ρ:Measure OrderPoint).support ∧
      0<(q:ℝ) ∧ (q:ℝ)<1 ∧
      q∈(ρ:Measure OrderPoint).support ∧
      (∀ t∈(ρ:Measure OrderPoint).support,t≤q) ∧
      1-(q:ℝ)≤1/(β:ℝ) ∧
      SKQAOA.Pstar-(1/4+Real.log 2)/(β:ℝ)≤
        ∫ t in (0:ℝ)..(q:ℝ),
          (ofMeasure β ρ).expectedCurvature brownianMeasure brownianMotion hbp t := by
  have hbp : 0<β := by exact_mod_cast (zero_lt_one.trans hβ)
  obtain ⟨ρ,hρ,hval⟩ := exists_minimizing_Parisi_measure hbp
  obtain ⟨q,hq0,hq1,hq,hqmax,hqbd⟩ := minimizingParisi_support_boundary hβ hρ
  exact ⟨ρ,q,hbp,hρ,hval,minimizingParisi_zero_in_support hbp hρ,
    hq0,hq1,hq,hqmax,hqbd,
    minimizingParisi_value_at_endpoint brownianMotion_isBrownian hbp hρ hq hqmax hq0 hq1⟩

end ParisiFinite

 

 

 

open MeasureTheory Set Filter
open scoped Topology
namespace ParisiGapGeometry
abbrev OrderPoint := Icc (0 : ℝ) 1

theorem support_gap_endpoints (μ : Measure OrderPoint) [IsProbabilityMeasure μ]
    {q : OrderPoint} (hz : (⟨0, by simp⟩ : OrderPoint) ∈ μ.support)
    (hq : q ∈ μ.support) (hmax : ∀ t ∈ μ.support, t ≤ q)
    (hne : μ.support ≠ Iic q) :
    ∃ a b : OrderPoint, a ∈ μ.support ∧ b ∈ μ.support ∧ a < b ∧ b ≤ q ∧
      ∀ x ∈ Ioo a b, x ∉ μ.support := by
  classical
  have hsub : μ.support ⊆ Iic q := fun t ht => hmax t ht
  obtain ⟨t, htq, ht⟩ := Set.exists_of_ssubset (ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hA : IsCompact (μ.support ∩ Iic t) := μ.isClosed_support.isCompact.inter_right isClosed_Iic
  have hB : IsCompact (μ.support ∩ Ici t) := μ.isClosed_support.isCompact.inter_right isClosed_Ici
  obtain ⟨a, ha⟩ := hA.exists_isGreatest ⟨⟨0, by simp⟩, hz, t.property.1⟩
  obtain ⟨b, hb⟩ := hB.exists_isLeast ⟨q, hq, htq⟩
  have hat : a < t := lt_of_le_of_ne ha.1.2 (by rintro rfl; exact ht ha.1.1)
  have htb : t < b := lt_of_le_of_ne hb.1.2 (by rintro rfl; exact ht hb.1.1)
  refine ⟨a, b, ha.1.1, hb.1.1, hat.trans htb, hmax b hb.1.1, ?_⟩
  intro x hx hs
  by_cases hxt : x ≤ t
  · exact (not_le.mpr hx.1) (ha.2 ⟨hs, hxt⟩)
  · exact (not_le.mpr hx.2) (hb.2 ⟨hs, (not_le.mp hxt).le⟩)

theorem cdf_constant_on_gap (μ : Measure OrderPoint) [IsProbabilityMeasure μ]
    {a b : OrderPoint} (hgap : ∀ x ∈ Ioo a b, x ∉ μ.support)
    {r : ℝ} (har : (a : ℝ) ≤ r) (hrb : r < (b : ℝ)) :
    μ {x | (x : ℝ) ≤ r} = μ (Iic a) := by
  apply measure_congr
  filter_upwards [μ.support_mem_ae] with x hx
  apply propext
  constructor
  · intro hxr
    by_contra hxa
    exact hgap x ⟨not_le.mp hxa, (show (x : ℝ) < (b : ℝ) from lt_of_le_of_lt hxr hrb)⟩ hx
  · intro hxa
    exact le_trans hxa har

theorem cdf_pos_at_gap_left (μ : Measure OrderPoint) [IsProbabilityMeasure μ]
    {a b : OrderPoint} (ha : a ∈ μ.support) (hab : a < b)
    (hgap : ∀ x ∈ Ioo a b, x ∉ μ.support) :
    0 < μ (Iic a) := by
  have hp : 0 < μ (Iio b) := (μ.mem_support_iff_forall a).mp ha _ (Iio_mem_nhds hab)
  have he : μ (Iio b) = μ (Iic a) := by
    apply measure_congr
    filter_upwards [μ.support_mem_ae] with x hx
    apply propext
    constructor
    · intro hxb
      by_contra hxa
      exact hgap x ⟨not_le.mp hxa, hxb⟩ hx
    · intro hxa
      exact lt_of_le_of_lt hxa hab
  rwa [he] at hp

end ParisiGapGeometry

end

end OAI
