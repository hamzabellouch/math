import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.TraceMassEndpoint

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

lemma timeMassDensity_stopping_joint_measurable (a : ℝ) (ha : 1/4<a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane =>
      timeMassDensity a q (S p.1) p.1 p.2.1) := by
  exact (timeMassDensity_joint_measurable a ha q hq hq1).comp
    (((hS.measurable'.comp measurable_fst).prodMk measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd))

 

def stoppedMassKernel (a q : ℝ) (S : ExactSLEGenerator.Driver → ℝ≥0∞) :
    Kernel ExactSLEGenerator.Driver UpperPlane :=
  (Kernel.const ExactSLEGenerator.Driver upperArea).withDensity
    (fun b z => timeMassDensity a q (S b) b z.1)

instance stoppedMassKernel_sfinite (a q : ℝ) (S : ExactSLEGenerator.Driver → ℝ≥0∞) :
    IsSFiniteKernel (stoppedMassKernel a q S) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun b z => (timeMassDensity_finite a q (S b) b z.1).ne)

lemma stoppedMassKernel_apply (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (b : ExactSLEGenerator.Driver) :
    stoppedMassKernel a q S b = actualUpperMass a q (S b) b :=
  Kernel.withDensity_apply _ (timeMassDensity_stopping_joint_measurable a ha q hq hq1 S hS) b

lemma actualUpperMass_measurable_stopping (a : ℝ) (ha : 1/4<a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    Measurable (fun b => actualUpperMass a q (S b) b) := by
  have he : (fun b => actualUpperMass a q (S b) b) =
      (fun b => stoppedMassKernel a q S b) :=
    funext (fun b => (stoppedMassKernel_apply a ha q hq hq1 S hS b).symm)
  rw [he]
  exact (stoppedMassKernel a q S).measurable

lemma actualUpperMass_add_unhit (a : ℝ) (ha : 1/4<a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (b : ExactSLEGenerator.Driver) :
    actualUpperMass a q ∞ b = actualUpperMass a q (S b) b + unhitMassKernel a q S b := by
  rw [unhitMassKernel_apply a ha q hq hq1 S hS]
  unfold actualUpperMass
  have he : (fun z : UpperPlane => timeMassDensity a q ∞ b z.1) =
      (fun z => timeMassDensity a q (S b) b z.1) +
      (fun z => ENNReal.ofReal (unhitMassDensity a q (S b) b z)) :=
    funext (fun z => timeMassDensity_add_unhit a q (S b) b z)
  rw [he,withDensity_add_left]
  exact (timeMassDensity_stopping_joint_measurable a ha q hq hq1 S hS).comp
    (measurable_const.prodMk measurable_id)

 

theorem actualUpperMass_stopped_random_test (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞)
    (hH : Measurable[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] H) :
    (∫⁻b, ∫⁻z, H (b,z) ∂actualUpperMass a q ∞ b ∂W) =
      (∫⁻b, ∫⁻z, H (b,z) ∂actualUpperMass a q (S b) b ∂W) +
      ∫⁻b, ∫⁻z, H (b,z) * ENNReal.ofReal (stoppedRemainingDensity a q (S b) b z.1) ∂upperArea ∂W := by
  have hH₀ : Measurable H := hH.mono (prod_sigma_le hS.measurableSpace_le _) le_rfl
  have hmeas : Measurable (fun b => ∫⁻z, H (b,z) ∂actualUpperMass a q (S b) b) := by
    simpa only [stoppedMassKernel_apply a ha q hq hq1 S hS] using
      hH₀.lintegral_kernel_prod_right' (κ := stoppedMassKernel a q S)
  simp_rw [actualUpperMass_add_unhit a ha q hq hq1 S hS, lintegral_add_measure]
  rw [lintegral_add_left hmeas, unhitMassKernel_random_test a ha W hW q hq hq1 S hS H hH]
  congr 1
  apply lintegral_congr
  intro b
  rw [stoppedRemainingKernel_apply a ha q hq hq1 S hS,
    lintegral_withDensity_eq_lintegral_mul]
  · exact lintegral_congr (fun z => mul_comm _ _)
  · exact ((stoppedRemainingDensity_joint_measurable a ha q hq hq1 S hS).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  · exact hH₀.comp (measurable_const.prodMk measurable_id)

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped Classical NNReal ENNReal

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

lemma remainingMassDensity_antitone_level (a : ℝ) (ha : 0<a) (t : ℝ≥0)
    (b : ExactSLEGenerator.Driver) (z : UpperPlane)
    (q r : ℝ) (hq : 0<q) (hqr : q≤r) (hr : r≤1) :
    remainingMassDensity a r t b z.1 ≤ remainingMassDensity a q t b z.1 := by
  have hT := radialTime_antitone a ha z.1 z.2 _ _ (mul_pos z.2 hq)
    (mul_le_mul_of_nonneg_left hqr z.2.le) (mul_le_of_le_one_right z.2.le hr) b
  simp only [remainingMassDensity,ite_eq_left z.2,radialRemaining]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  split_ifs with hr hq hq
  · exact le_rfl
  · exact False.elim (hq ⟨hr.1,hr.2.trans_le hT⟩)
  · unfold physicalGreen
    positivity
  · exact le_rfl

lemma stoppedRemainingDensity_antitone_level (a : ℝ) (ha : 0<a) (t : ℝ≥0∞)
    (b : ExactSLEGenerator.Driver) (z : UpperPlane)
    (q r : ℝ) (hq : 0<q) (hqr : q≤r) (hr : r≤1) :
    stoppedRemainingDensity a r t b z.1 ≤ stoppedRemainingDensity a q t b z.1 := by
  unfold stoppedRemainingDensity
  split_ifs
  · exact le_rfl
  · exact remainingMassDensity_antitone_level a ha t.toNNReal b z q r hq hqr hr

lemma remainingMassDensity_eventually_eq_surviving (a : ℝ) (ha : 0<a) (t : ℝ≥0)
    (q : ℕ → ℝ) (hq : ∀ n, 0<q n ∧ q n≤1) (hlim : Tendsto q atTop (𝓝 0))
    (b : ExactSLEGenerator.Driver) (z : UpperPlane) :
    ∀ᶠ n in atTop, remainingMassDensity a (q n) t b z.1 = survivingGreen a t b z.1 := by
  by_cases ht : alive a b.1 t z.1
  · have hR := physicalRadius_actual_pos a b z.1 t ht
    have hqR : ∀ᶠ n in atTop, z.1.im*q n<physicalRadius (actualState a b.1 t z.1) := by
      have hconv : Tendsto (fun n => z.1.im*q n) atTop (𝓝 0) := by simpa using hlim.const_mul z.1.im
      exact hconv.eventually (gt_mem_nhds hR)
    filter_upwards [hqR] with n hn
    have hnT : (t : ℝ≥0∞)<radialTime a b.1 z.1 (z.1.im*q n) := by
      by_contra h
      have hTt := le_of_not_gt h
      have hfin : radialTime a b.1 z.1 (z.1.im*q n)≠∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hTt
      have hle : (radialTime a b.1 z.1 (z.1.im*q n)).toNNReal≤t := by
        exact ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_toNNReal hfin] using hTt)
      have hh := (radialTime_attained a ha z.1 z.2 _ (mul_pos z.2 (hq n).1)
        (mul_le_of_le_one_right z.2.le (hq n).2) b hfin).2
      have he := physicalRadius_actual_anti a ha b z.1 _ t hle ht
      rw [hh] at he
      exact not_le.mpr hn he
    simp only [remainingMassDensity,ite_eq_left z.2,radialRemaining,ht,hnT,and_self,ite_true,
      survivingGreen]
  · filter_upwards [] with n
    simp only [remainingMassDensity,ite_eq_left z.2,radialRemaining,ht,false_and,ite_false,
      survivingGreen,mul_zero]

lemma stoppedRemainingDensity_eventually_eq_surviving (a : ℝ) (ha : 0<a) (t : ℝ≥0∞)
    (q : ℕ → ℝ) (hq : ∀ n, 0<q n ∧ q n≤1) (hlim : Tendsto q atTop (𝓝 0))
    (b : ExactSLEGenerator.Driver) (z : UpperPlane) :
    ∀ᶠ n in atTop, stoppedRemainingDensity a (q n) t b z.1 = stoppedSurvivingGreen a t b z.1 := by
  unfold stoppedRemainingDensity stoppedSurvivingGreen
  by_cases ht : t=∞
  · simp only [ht,ite_true,eventually_const]
  · simp only [ite_eq_right ht]
    exact remainingMassDensity_eventually_eq_surviving a ha t.toNNReal q hq hlim b z

 

theorem stoppedRemainingDensity_random_test_tendsto (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver)
    (q : ℕ → ℝ) (hq : ∀ n, 0<q n ∧ q n≤1) (hanti : Antitone q)
    (hlim : Tendsto q atTop (𝓝 0))
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞) (hH : Measurable H) :
    Tendsto (fun n => ∫⁻b, ∫⁻z, H (b,z)*
        ENNReal.ofReal (stoppedRemainingDensity a (q n) (S b) b z.1) ∂upperArea ∂W)
      atTop (𝓝 (∫⁻b, ∫⁻z, H (b,z)*
        ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1) ∂upperArea ∂W)) := by
  have hm (n : ℕ) : Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane =>
      H p*ENNReal.ofReal (stoppedRemainingDensity a (q n) (S p.1) p.1 p.2.1)) :=
    hH.mul (stoppedRemainingDensity_joint_measurable a ha (q n) (hq n).1 (hq n).2 S hS).ennreal_ofReal
  have hmono (b : ExactSLEGenerator.Driver) (z : UpperPlane) :
      Monotone (fun n => H (b,z)*ENNReal.ofReal (stoppedRemainingDensity a (q n) (S b) b z.1)) := by
    intro i j hij
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal
      (stoppedRemainingDensity_antitone_level a (by linarith) (S b) b z
        (q j) (q i) (hq j).1 (hanti hij) (hq i).2)) _
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    exact (hm n).lintegral_prod_right'.aemeasurable
  · exact Eventually.of_forall (fun b i j hij => lintegral_mono (fun z => hmono b z hij))
  · filter_upwards [] with b
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n
      exact ((hm n).comp (measurable_const.prodMk measurable_id)).aemeasurable
    · exact Eventually.of_forall (hmono b)
    · filter_upwards [] with z
      apply tendsto_const_nhds.congr'
      filter_upwards [stoppedRemainingDensity_eventually_eq_surviving a (by linarith)
        (S b) q hq hlim b z] with n hn
      rw [hn]

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

 

theorem actual_stopped_remaining_spatial_L1 (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (K : Set UpperPlane) (hK : MeasurableSet K)
    (hKfin : upperArea K<∞) (c : ℝ) (hc : 0<c) (hcK : ∀ z∈K,c≤z.1.im)
    (f : UpperPlane → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0≤B) (hfB : ∀z∈K,‖f z‖≤B)
    (q : ℕ → ℝ) (hq : ∀n,0<q n ∧ q n≤1) (hlim : Tendsto q atTop (𝓝 0)) :
    Integrable (fun p : UpperPlane × ExactSLEGenerator.Driver => f p.1*stoppedSurvivingGreen a (S p.2) p.2 p.1.1)
      ((upperArea.restrict K).prod W) ∧
    Tendsto (fun n => ∫p : UpperPlane × ExactSLEGenerator.Driver,
      ‖f p.1*stoppedRemainingDensity a (q n) (S p.2) p.2 p.1.1-f p.1*stoppedSurvivingGreen a (S p.2) p.2 p.1.1‖
      ∂((upperArea.restrict K).prod W)) atTop (𝓝 0)
 := by
  let ν := upperArea.restrict K
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using hKfin⟩
  let F : UpperPlane × ExactSLEGenerator.Driver → ℝ := fun p => f p.1*stoppedSurvivingGreen a (S p.2) p.2 p.1.1
  let H : ℕ → UpperPlane × ExactSLEGenerator.Driver → ℝ := fun n p => f p.1*stoppedRemainingDensity a (q n) (S p.2) p.2 p.1.1
  have hHm (n : ℕ) : Measurable (H n) :=
    (hf.comp measurable_fst).mul ((stoppedRemainingDensity_joint_measurable a ha (q n) (hq n).1 (hq n).2 S hS).comp measurable_swap)
  have hconv (p : UpperPlane × ExactSLEGenerator.Driver) : Tendsto (fun n => H n p) atTop (𝓝 (F p)) :=
    (stopped_remaining_to_surviving a ha (S p.2) q hq hlim p.2 p.1.1 p.1.2).const_mul (f p.1)
  have hFm : Measurable F := measurable_of_tendsto_metrizable hHm (tendsto_pi_nhds.mpr hconv)
  have hi (z : UpperPlane) : Integrable (fun b => F (z,b)) W :=
    (survivingGreen_optional_bound a ha W hW z S hS).1.const_mul (f z)
  have he (z : UpperPlane) : (∫b,‖F (z,b)‖∂W) = ‖f z‖*(∫b,stoppedSurvivingGreen a (S b) b z.1∂W) := by
    simp only [F,norm_mul,Real.norm_of_nonneg (stoppedSurvivingGreen_nonneg _ _ _ _),integral_const_mul]
  let C := Real.exp (-alpha a*Real.log 2)*Real.exp (-alpha a*Real.log c)
  have hC : 0≤C := by dsimp [C]; positivity
  have hb (z : UpperPlane) (hz : z∈K) : (∫b,‖F (z,b)‖∂W)≤B*C := by
    rw [he]
    have hG := (survivingGreen_optional_bound a ha W hW z S hS).2
    have hgreen : physicalGreen a (z.1,0)≤Real.exp (-alpha a*Real.log c) := by
      apply physicalGreen_bound a c ha hc _ z.2
      simpa [physicalRadius,Y] using hcK z hz
    have hpos : 0≤(∫b,stoppedSurvivingGreen a (S b) b z.1∂W) := integral_nonneg (fun b => stoppedSurvivingGreen_nonneg _ _ _ _)
    exact mul_le_mul (hfB z hz) (hG.trans (mul_le_mul_of_nonneg_left hgreen (Real.exp_pos _).le))
      hpos hB
  have hFi : Integrable F (ν.prod W) := by
    apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hi,?_⟩
    apply Integrable.of_bound (hFm.aestronglyMeasurable.norm.integral_prod_right') (B*C)
    filter_upwards [ae_restrict_mem hK] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg (fun b => norm_nonneg (F (z,b))))]
    exact hb z hz
  refine ⟨hFi,?_⟩
  have hD : Integrable (fun p => 2*‖F p‖) (ν.prod W) := hFi.norm.const_mul 2
  have hbound (n : ℕ) (p : UpperPlane × ExactSLEGenerator.Driver) : ‖H n p-F p‖≤2*‖F p‖ := by
    have hle : ‖H n p‖≤‖F p‖ := by
      dsimp only [H,F]
      rw [norm_mul,norm_mul,Real.norm_of_nonneg (stoppedRemainingDensity_nonneg _ _ _ _ _),
        Real.norm_of_nonneg (stoppedSurvivingGreen_nonneg _ _ _ _)]
      exact mul_le_mul_of_nonneg_left (stoppedRemainingDensity_le_surviving _ _ _ _ _ p.1.2) (norm_nonneg _)
    calc ‖H n p-F p‖≤‖H n p‖+‖F p‖ := norm_sub_le _ _
      _≤2*‖F p‖ := by linarith
  have hlim' := tendsto_integral_of_dominated_convergence (fun p => 2*‖F p‖)
    (fun n => ((hHm n).sub hFm).norm.aestronglyMeasurable) hD
    (fun n => Eventually.of_forall (fun p => by simpa using hbound n p))
    (Eventually.of_forall (fun p => by simpa using ((hconv p).sub_const (F p)).norm))
  simpa using hlim'

lemma actualUpper_stopped_remaining_integral_tendsto (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (f : C_c(UpperPlane,ℝ)) (U : Set ExactSLEGenerator.Driver)
    (q : ℕ → ℝ) (hq : ∀n,0<q n ∧ q n≤1) (hlim : Tendsto q atTop (𝓝 0)) :
    Tendsto (fun n => ∫b in U, (∫z : UpperPlane,f z*stoppedRemainingDensity a (q n) (S b) b z.1∂upperArea) ∂W)
      atTop (𝓝 (∫b in U, (∫z : UpperPlane,f z*stoppedSurvivingGreen a (S b) b z.1∂upperArea) ∂W)) := by
  let K := tsupport f
  have hK : IsCompact K := f.hasCompactSupport
  have hfin : upperArea K<∞ := by
    rw [upperArea,upper_embedding.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top
  have : IsFiniteMeasure (upperArea.restrict K) := ⟨by simpa using hfin⟩
  obtain ⟨c,hc,hcK⟩ := upper_compact_lower K hK
  obtain ⟨B,hB,hBf⟩ := upperExtension_bounded f
  have H := actual_stopped_remaining_spatial_L1 a ha W hW S hS K hK.measurableSet hfin (c/2) (by positivity)
    (fun z hz => by have := hcK z hz; linarith) f f.continuous.measurable B hB
    (fun z hz => by simpa only [upperExtension_apply] using hBf z.1 ⟨z,hz,rfl⟩) q hq hlim
  let F : UpperPlane × ExactSLEGenerator.Driver → ℝ := fun p => f p.1*stoppedSurvivingGreen a (S p.2) p.2 p.1.1
  let R : ℕ → UpperPlane × ExactSLEGenerator.Driver → ℝ := fun n p => f p.1*stoppedRemainingDensity a (q n) (S p.2) p.2 p.1.1
  let μ := (upperArea.restrict K).prod (W.restrict U)
  have hFi : Integrable F μ := H.1.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hRm (n : ℕ) : Measurable (R n) :=
    (f.continuous.measurable.comp measurable_fst).mul
      ((stoppedRemainingDensity_joint_measurable a ha (q n) (hq n).1 (hq n).2 S hS).comp measurable_swap)
  have hbound (n : ℕ) (p : UpperPlane × ExactSLEGenerator.Driver) : ‖R n p‖≤‖F p‖ := by
    dsimp only [R,F]
    rw [norm_mul,norm_mul,Real.norm_of_nonneg (stoppedRemainingDensity_nonneg _ _ _ _ _),
      Real.norm_of_nonneg (stoppedSurvivingGreen_nonneg _ _ _ _)]
    exact mul_le_mul_of_nonneg_left (stoppedRemainingDensity_le_surviving _ _ _ _ _ p.1.2) (norm_nonneg _)
  have hRi (n : ℕ) : Integrable (R n) μ := hFi.norm.mono' (hRm n).aestronglyMeasurable
    (Eventually.of_forall (hbound n))
  have ht := tendsto_integral_of_dominated_convergence (fun p => ‖F p‖)
    (fun n => (hRm n).aestronglyMeasurable) hFi.norm (fun n => Eventually.of_forall (hbound n))
    (Eventually.of_forall (fun p => (stopped_remaining_to_surviving a ha (S p.2) q hq hlim p.2 p.1.1 p.1.2).const_mul (f p.1)))
  have he (g : UpperPlane → ℝ) : (∫z in K,f z*g z∂upperArea) = ∫z,f z*g z∂upperArea :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [image_eq_zero_of_notMem_tsupport hz,zero_mul])
  have hRint (n : ℕ) : (∫p,R n p∂μ) = ∫b in U,(∫z : UpperPlane,f z*stoppedRemainingDensity a (q n) (S b) b z.1∂upperArea)∂W := by
    rw [integral_prod_symm (R n) (hRi n)]
    apply integral_congr_ae
    filter_upwards [] with b
    exact he _
  have hFint : (∫p,F p∂μ) = ∫b in U,(∫z : UpperPlane,f z*stoppedSurvivingGreen a (S b) b z.1∂upperArea)∂W := by
    rw [integral_prod_symm F hFi]
    apply integral_congr_ae
    filter_upwards [] with b
    exact he _
  change Tendsto (fun n => ∫p,R n p∂μ) atTop (𝓝 (∫p,F p∂μ)) at ht
  simpa only [hRint,hFint] using ht

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

lemma actualUpperMass_stopped_norm_bound (a : ℝ) (ha : 1/4<a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1) (t : ℝ≥0∞)
    (b : ExactSLEGenerator.Driver) (f : C_c(UpperPlane,ℝ)) :
    ‖∫z, f z ∂actualUpperMass a q t b‖ ≤
      ∫z, ‖f z‖ ∂actualUpperMass a q ∞ b := by
  have := actualUpperMass_finiteOnCompacts a ha q hq hq1 ∞ b
  exact (norm_integral_le_integral_norm _).trans (integral_mono_measure
    (actualUpperMass_mono_time a q b le_top) (Eventually.of_forall (fun _ => norm_nonneg _))
    f.integrable.norm)

 

theorem actualUpperMass_stopped_Lp_bound (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (m : ℕ) (hm : 1 ≤ m) (f : C_c(UpperPlane,ℝ)) :
    ∃ C : ℝ≥0∞, C<∞ ∧ ∀ q : ℝ, 0<q → q≤1 →
      ∀ S : ExactSLEGenerator.Driver → ℝ≥0∞, IsStoppingTime rawFiltration S →
      MemLp (fun b => ∫z, f z ∂actualUpperMass a q (S b) b) (m : ℝ≥0∞) W ∧
      eLpNorm (fun b => ∫z, f z ∂actualUpperMass a q (S b) b) (m : ℝ≥0∞) W ≤ C := by
  let g : C_c(UpperPlane,ℝ) := ⟨⟨fun z => ‖f z‖,f.continuous.norm⟩,f.hasCompactSupport.norm⟩
  obtain ⟨C,hC,hCb⟩ := actualUpperMass_Lp_bound a ha W hW m hm g
  refine ⟨C,hC,fun q hq hq1 S hS => ?_⟩
  have hmeas : StronglyMeasurable (fun b => ∫z, f z ∂actualUpperMass a q (S b) b) := by
    simpa [stoppedMassKernel_apply a ha q hq hq1 S hS] using
      (f.continuous.measurable.stronglyMeasurable.integral_kernel
        (κ := stoppedMassKernel a q S))
  have hb : ∀ᵐ b ∂W, ‖∫z, f z ∂actualUpperMass a q (S b) b‖ ≤
      ∫z, g z ∂actualUpperMass a q ∞ b :=
    Eventually.of_forall (fun b => actualUpperMass_stopped_norm_bound a ha q hq hq1 (S b) b f)
  refine ⟨(hCb q hq hq1 ∞).1.mono' hmeas.aestronglyMeasurable hb,?_⟩
  exact (eLpNorm_mono_ae hmeas.aestronglyMeasurable (hb.mono (fun _ h => h.trans (le_abs_self _)))).trans
    (hCb q hq hq1 ∞).2

lemma actualUpperMass_stopped_eval_integrable (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (f : C_c(UpperPlane,ℝ)) :
    Integrable (fun b => ∫z, f z ∂actualUpperMass a q (S b) b) W := by
  obtain ⟨C,hC,hCb⟩ := actualUpperMass_stopped_Lp_bound a ha W hW 1 le_rfl f
  exact (hCb q hq hq1 S hS).1.integrable (by norm_num)

lemma stoppedRemainingKernel_compact_eval (a : ℝ) (ha : 1/4<a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (b : ExactSLEGenerator.Driver) (f : C_c(UpperPlane,ℝ)) :
    (∫z, f z ∂stoppedRemainingKernel a q S b) =
      ∫z, f z*stoppedRemainingDensity a q (S b) b z.1 ∂upperArea := by
  rw [stoppedRemainingKernel_apply a ha q hq hq1 S hS,
    integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (stoppedRemainingDensity_nonneg _ _ _ _ _), smul_eq_mul, mul_comm]
  · exact ((stoppedRemainingDensity_joint_measurable a ha q hq hq1 S hS).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  · exact Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

 

theorem actualUpperMass_stopped_finite_kernel (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (f : C_c(UpperPlane,ℝ))
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    (∫b in U, (∫z, f z ∂actualUpperMass a q ∞ b)-(∫z, f z ∂actualUpperMass a q (S b) b) ∂W) =
      ∫b in U, (∫z : UpperPlane, f z*stoppedRemainingDensity a q (S b) b z.1 ∂upperArea) ∂W := by
  have := unhitMassKernel_average_finiteOnCompacts a ha W hW q hq hq1 S hS
  have := stoppedRemainingKernel_average_finiteOnCompacts a ha W hW q hq hq1 S hS
  have := average_restrict_finite (unhitMassKernel a q S) W U
  have := average_restrict_finite (stoppedRemainingKernel a q S) W U
  have he (b : ExactSLEGenerator.Driver) :
      (∫z, f z ∂actualUpperMass a q ∞ b)-(∫z, f z ∂actualUpperMass a q (S b) b) =
        ∫z, f z ∂unhitMassKernel a q S b := by
    have := actualUpperMass_finiteOnCompacts a ha q hq hq1 ∞ b
    have hi : Integrable f (actualUpperMass a q (S b) b + unhitMassKernel a q S b) := by
      rw [← actualUpperMass_add_unhit a ha q hq hq1 S hS]
      exact f.integrable
    rw [actualUpperMass_add_unhit a ha q hq hq1 S hS, integral_add_measure
      (integrable_add_measure.mp hi).1 (integrable_add_measure.mp hi).2]
    ring
  simp_rw [he]
  rw [← average_compact_eval_of_average_finite,
    unhitMassKernel_conditional_average a ha W hW q hq hq1 S hS U hU,
    average_compact_eval_of_average_finite]
  exact integral_congr_ae (Eventually.of_forall (fun b =>
    stoppedRemainingKernel_compact_eval a ha q hq hq1 S hS b f))

 

theorem actualUpperMass_stopped_convex_potential_limit (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℕ → ℝ) (hq : ∀ n, 0<q n ∧ q n≤1) (hlim : Tendsto q atTop (𝓝 0))
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
    (hs : ∀ k j, j∈s k → k≤j) (hc : ∀ k j, j∈s k → 0≤c k j)
    (hsum : ∀ k, ∑j∈s k,c k j=1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (f : C_c(UpperPlane,ℝ))
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    Tendsto (fun k => ∫b in U,
      ∑j∈s k,c k j*((∫z, f z ∂actualUpperMass a (q j) ∞ b)-
        (∫z, f z ∂actualUpperMass a (q j) (S b) b)) ∂W)
      atTop (𝓝 (∫b in U, (∫z : UpperPlane, f z*stoppedSurvivingGreen a (S b) b z.1 ∂upperArea) ∂W)) := by
  have hpot := actualUpper_stopped_remaining_integral_tendsto a ha W hW S hS f U q hq hlim
  have hcombo := scalar_convex_tail_limit s c hs hc hsum _ _ hpot
  have he (k : ℕ) : (∫b in U,
      ∑j∈s k,c k j*((∫z, f z ∂actualUpperMass a (q j) ∞ b)-
        (∫z, f z ∂actualUpperMass a (q j) (S b) b)) ∂W) =
      ∑j∈s k,c k j*(∫b in U,
        (∫z : UpperPlane, f z*stoppedRemainingDensity a (q j) (S b) b z.1 ∂upperArea) ∂W) := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul, actualUpperMass_stopped_finite_kernel a ha W hW
        (q j) (hq j).1 (hq j).2 S hS f U hU]
    · intro j hj
      exact (((actualUpperMass_stopped_eval_integrable a ha W hW (q j) (hq j).1 (hq j).2
        (fun _ => ∞) (fun t => by simp) f).sub
        (actualUpperMass_stopped_eval_integrable a ha W hW (q j) (hq j).1 (hq j).2 S hS f)).const_mul
        (c k j)).restrict
  simpa only [he] using hcombo

end ExactSLEGreen
end
end

end OAI
