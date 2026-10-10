import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.SurvivalLocalization

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
open Filter
open Filter Set
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MeasureTheory
open scoped Classical
open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Topology
open scoped ENNReal
open Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Topology
open MeasureTheory Filter Topology Set CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter ExactSLEGenerator ExactSLEMain
open scoped Classical NNReal ENNReal Topology
theorem actual_surviving_green (a : ℝ) (ha : 1/4<a) (t : ℝ≥0) :
    (letI : MeasurableSpace ExactSLEGenerator.Driver := rawFiltration t
     Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane => survivingGreen a t p.1 p.2.1)) ∧
    (∀ (q : ℕ → ℝ), (∀n,0<q n ∧ q n≤1) → Tendsto q atTop (𝓝 0) →
      ∀ (b : ExactSLEGenerator.Driver) (z : ℂ), 0<z.im →
      Tendsto (fun n => remainingMassDensity a (q n) t b z) atTop (𝓝 (survivingGreen a t b z))) ∧
    ∀ (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
      IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W →
      ∀ (z : ℂ), 0<z.im → Integrable (fun b => survivingGreen a t b z) W ∧
      (∫b, survivingGreen a t b z ∂W) ≤ Real.exp (-alpha a*Real.log 2)*physicalGreen a (z,0)
 := by
  let q : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hq (n : ℕ) : 0<q n ∧ q n≤1 := by
    dsimp [q]
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hlim : Tendsto q atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hm : letI : MeasurableSpace ExactSLEGenerator.Driver := rawFiltration t
      Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane => survivingGreen a t p.1 p.2.1) := by
    let : MeasurableSpace ExactSLEGenerator.Driver := rawFiltration t
    apply measurable_of_tendsto_metrizable (f:=fun n p => remainingMassDensity a (q n) t p.1 p.2.1)
    · intro n
      have H := (radialRemaining_raw_joint a ha (q n) (hq n).1 (hq n).2 t).const_mul
        (Real.exp (-alpha a*Real.log 2))
      convert H using 1
      funext p
      simp only [remainingMassDensity,ite_eq_left p.2.2]
    · exact tendsto_pi_nhds.mpr (fun p => remaining_to_surviving a ha t q hq hlim p.1 p.2.1 p.2.2)
  refine ⟨hm,fun q hq hlim => remaining_to_surviving a ha t q hq hlim,?_⟩
  intro W inst hW z hz
  let F : ℕ → ExactSLEGenerator.Driver → ℝ := fun n b => remainingMassDensity a (q n) t b z
  let G : ExactSLEGenerator.Driver → ℝ := fun b => survivingGreen a t b z
  let C : ℝ := Real.exp (-alpha a*Real.log 2)*physicalGreen a (z,0)
  have hC : 0≤C := by unfold C physicalGreen; positivity
  have hFi (n : ℕ) := (remainingMassDensity_mean_bound a ha W hW (q n) (hq n).1 (hq n).2 t z hz).1
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) W := (hFi n).aestronglyMeasurable
  have hconv : ∀ᵐ b ∂W,Tendsto (fun n => F n b) atTop (𝓝 (G b)) :=
    Eventually.of_forall (fun b => remaining_to_surviving a ha t q hq hlim b z hz)
  have hbound (n : ℕ) : eLpNorm (F n) 1 W≤ENNReal.ofReal C := by
    rw [eLpNorm_one_eq_lintegral_enorm (hFm n),←ofReal_integral_norm_eq_lintegral_enorm (hFi n)]
    have he : (fun b => ‖F n b‖) = F n := by
      funext b
      exact Real.norm_of_nonneg (remainingMassDensity_nonneg a (q n) t b z)
    rw [he]
    exact ENNReal.ofReal_le_ofReal
      (remainingMassDensity_mean_bound a ha W hW (q n) (hq n).1 (hq n).2 t z hz).2
  have hGm := aestronglyMeasurable_of_tendsto_ae atTop hFm hconv
  have hGb := Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hbound) hFm hGm hconv
  have hGi : Integrable G W := memLp_one_iff_integrable.mp (hGb.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hGi,?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm hGm,←ofReal_integral_norm_eq_lintegral_enorm hGi] at hGb
  have he : (fun b => ‖G b‖) = G := by
    funext b
    exact Real.norm_of_nonneg (survivingGreen_nonneg a t b z)
  rw [he] at hGb
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hGb
end ExactSLEGreen

namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set ExactSLEGenerator ExactSLEMain
open scoped Classical NNReal ENNReal Topology
lemma remainingMassDensity_le_surviving (a q : ℝ) (t : ℝ≥0)
    (b : ExactSLEGenerator.Driver) (z : ℂ) (hz : 0<z.im) :
    remainingMassDensity a q t b z ≤ survivingGreen a t b z := by
  unfold remainingMassDensity radialRemaining survivingGreen
  simp only [ite_eq_left hz]
  by_cases ht : alive a b.1 t z
  · simp only [ht,true_and,ite_true]
    split_ifs
    · exact le_rfl
    · simpa only [mul_zero] using (show 0≤Real.exp (-alpha a*Real.log 2)*physicalGreen a (actualState a b.1 t z) from by unfold physicalGreen; positivity)
  · simp only [ht,false_and,ite_false,mul_zero,le_refl]
end ExactSLEGreen
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set ExactSLEGenerator ExactSLEMain
open scoped NNReal ENNReal Topology
 

theorem actual_remaining_spatial_L1 (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℝ≥0) (K : Set UpperPlane) (hK : MeasurableSet K)
    (hKfin : upperArea K<∞) (c : ℝ) (hc : 0<c) (hcK : ∀ z∈K,c≤z.1.im)
    (f : UpperPlane → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0≤B) (hfB : ∀z∈K,‖f z‖≤B)
    (q : ℕ → ℝ) (hq : ∀n,0<q n ∧ q n≤1) (hlim : Tendsto q atTop (𝓝 0)) :
    Integrable (fun p : UpperPlane × ExactSLEGenerator.Driver => f p.1*survivingGreen a t p.2 p.1.1)
      ((upperArea.restrict K).prod W) ∧
    Tendsto (fun n => ∫p : UpperPlane × ExactSLEGenerator.Driver,
      ‖f p.1*remainingMassDensity a (q n) t p.2 p.1.1-f p.1*survivingGreen a t p.2 p.1.1‖
      ∂((upperArea.restrict K).prod W)) atTop (𝓝 0)
 := by
  let ν := upperArea.restrict K
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using hKfin⟩
  let F : UpperPlane × ExactSLEGenerator.Driver → ℝ := fun p => f p.1*survivingGreen a t p.2 p.1.1
  let H : ℕ → UpperPlane × ExactSLEGenerator.Driver → ℝ := fun n p => f p.1*remainingMassDensity a (q n) t p.2 p.1.1
  have hHm (n : ℕ) : Measurable (H n) :=
    (hf.comp measurable_fst).mul ((remainingMassDensity_measurable a ha (q n) (hq n).1 (hq n).2 t).comp
      (measurable_snd.prodMk (measurable_subtype_coe.comp measurable_fst)))
  have hconv (p : UpperPlane × ExactSLEGenerator.Driver) : Tendsto (fun n => H n p) atTop (𝓝 (F p)) :=
    (remaining_to_surviving a ha t q hq hlim p.2 p.1.1 p.1.2).const_mul (f p.1)
  have hFm : Measurable F := measurable_of_tendsto_metrizable hHm (tendsto_pi_nhds.mpr hconv)
  have hi (z : UpperPlane) : Integrable (fun b => F (z,b)) W :=
    ((actual_surviving_green a ha t).2.2 W hW z.1 z.2).1.const_mul (f z)
  have he (z : UpperPlane) : (∫b,‖F (z,b)‖∂W) = ‖f z‖*(∫b,survivingGreen a t b z.1∂W) := by
    simp only [F,norm_mul,Real.norm_of_nonneg (survivingGreen_nonneg _ _ _ _),integral_const_mul]
  let C := Real.exp (-alpha a*Real.log 2)*Real.exp (-alpha a*Real.log c)
  have hC : 0≤C := by dsimp [C]; positivity
  have hb (z : UpperPlane) (hz : z∈K) : (∫b,‖F (z,b)‖∂W)≤B*C := by
    rw [he]
    have hG := ((actual_surviving_green a ha t).2.2 W hW z.1 z.2).2
    have hgreen : physicalGreen a (z.1,0)≤Real.exp (-alpha a*Real.log c) := by
      apply physicalGreen_bound a c ha hc _ z.2
      simpa [physicalRadius,Y] using hcK z hz
    have hpos : 0≤(∫b,survivingGreen a t b z.1∂W) := integral_nonneg (fun b => survivingGreen_nonneg _ _ _ _)
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
      rw [norm_mul,norm_mul,Real.norm_of_nonneg (remainingMassDensity_nonneg _ _ _ _ _),
        Real.norm_of_nonneg (survivingGreen_nonneg _ _ _ _)]
      exact mul_le_mul_of_nonneg_left (remainingMassDensity_le_surviving _ _ _ _ _ p.1.2) (norm_nonneg _)
    calc ‖H n p-F p‖≤‖H n p‖+‖F p‖ := norm_sub_le _ _
      _≤2*‖F p‖ := by linarith
  have hlim' := tendsto_integral_of_dominated_convergence (fun p => 2*‖F p‖)
    (fun n => ((hHm n).sub hFm).norm.aestronglyMeasurable) hD
    (fun n => Eventually.of_forall (fun p => by simpa using hbound n p))
    (Eventually.of_forall (fun p => by simpa using ((hconv p).sub_const (F p)).norm))
  simpa using hlim'
end ExactSLEGreen

namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction
open scoped Classical NNReal ENNReal
lemma actualMassEval_raw_measurable (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (t : ℝ≥0) (K : Set ℂ) (f : ℂ → ℝ) (hf : Measurable f) :
    Measurable[rawFiltration t] (actualMassEval a q t K f) := by
  have hD := timeMassDensity_raw_joint a ha q hq hq1 t
  let : MeasurableSpace ExactSLEGenerator.Driver := rawFiltration t
  have hm : Measurable (fun p : ExactSLEGenerator.Driver × ℂ => f p.2*(timeMassDensity a q t p.1 p.2).toReal) :=
    (hf.comp measurable_snd).mul hD.ennreal_toReal
  exact hm.stronglyMeasurable.integral_prod_right'.measurable
lemma actualUpperMass_eval_raw_measurable (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (t : ℝ≥0) (f : C_c(UpperPlane,ℝ)) :
    Measurable[rawFiltration t] (fun b => ∫z,f z∂actualUpperMass a q t b) := by
  simp_rw [actualUpperMass_eval a ha q hq hq1]
  exact actualMassEval_raw_measurable a ha q hq hq1 t _ _ (upperExtension_measurable f)
lemma raw_ae_measurable_limit {Ω : Type*} {m m₀ : MeasurableSpace Ω} (W : Measure[m₀] Ω)
    (F : ℕ → Ω → ℝ) (g : Ω → ℝ) (hF : ∀ k, Measurable[m] (F k))
    (h : ∀ᵐ b ∂W, Tendsto (fun k => F k b) atTop (𝓝 (g b))) :
    AEStronglyMeasurable[m] g W := by
  refine ⟨fun b => limsup (fun k => F k b) atTop, (Measurable.limsup hF).stronglyMeasurable,?_⟩
  filter_upwards [h] with b hb
  exact hb.limsup_eq.symm
 

theorem actual_radon_raw_evaluations (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ)
      (μ : ExactSLEGenerator.Driver → ℕ → Measure UpperPlane),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k j, j∈s k → 0≤coeff k j) ∧
      (∀ k, ∑ j∈s k, coeff k j=1) ∧
      (∀ b i, IsFiniteMeasureOnCompacts (μ b i) ∧ (μ b i).Regular) ∧
      (∀ i (f : C_c(UpperPlane, ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ b i) (m : ℝ≥0∞) W) ∧
      (∀ i (f : C_c(UpperPlane, ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k, coeff k j *
            ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            - ∫z,f z∂μ b i) 1 W) atTop (𝓝 0)) ∧
      (∀ i, t i=∞ → ∀ f : C_c(UpperPlane,ℝ),
        (∫b, (∫z,f z∂μ b i) ∂W) = ∫z : UpperPlane,
          f z * (Real.exp (-alpha a*Real.log 2)*physicalGreen a (z.1,0)) ∂upperArea) ∧
      (∀ i (t₀ : ℝ≥0), t i=t₀ → ∀ f : C_c(UpperPlane,ℝ),
        AEStronglyMeasurable[rawFiltration t₀] (fun b => ∫z,f z∂μ b i) W) ∧
      ∀ᵐ b ∂W,
        (∀ i j, t i ≤ t j → μ b i ≤ μ b j) ∧
        (∀ i (f : C_c(UpperPlane, ℝ)),
          Tendsto (fun k => ∑ j∈s k, coeff k j *
            ∫ z, f z ∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫ z, f z ∂μ b i)))
 := by
  obtain ⟨s,c,μ,hs,hc,hsum,hμ,hmom,hL1,hmean,h⟩ := actual_radon_terminal_mean a ha W hW t
  refine ⟨s,c,μ,hs,hc,hsum,hμ,hmom,hL1,hmean,?_,h⟩
  intro i t₀ hi f
  apply raw_ae_measurable_limit W
    (fun k b => ∑ j∈s k,c k j*∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
    (fun b => ∫z,f z∂μ b i)
  · intro k
    rw [hi]
    apply Finset.measurable_sum
    intro j hj
    have hq1 : Real.exp (-2*a*(j+1))≤1 := by
      apply Real.exp_le_one_iff.mpr
      have ha0 : 0<a := by linarith
      have hj0 : (0:ℝ)≤j := Nat.cast_nonneg _
      nlinarith
    exact measurable_const.mul (actualUpperMass_eval_raw_measurable a ha _ (Real.exp_pos _) hq1 t₀ f)
  · filter_upwards [h] with b hb
    exact hb.2 i f
end ExactSLEGreen

namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction
open scoped Classical NNReal ENNReal Topology
lemma actualUpperMass_finite_kernel (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1) (t : ℝ≥0) (f : C_c(UpperPlane,ℝ))
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[rawFiltration t] U) :
    (∫b in U, (∫z,f z∂actualUpperMass a q ∞ b)-(∫z,f z∂actualUpperMass a q t b) ∂W) =
      ∫b in U, (∫z : UpperPlane,f z*remainingMassDensity a q t b z.1∂upperArea) ∂W := by
  let K := Subtype.val '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_subtype_val
  obtain ⟨c,hc,hcK⟩ := upper_compact_lower (tsupport f) f.hasCompactSupport
  simp_rw [actualUpperMass_eval a ha q hq hq1]
  rw [actual_finite_conditional_mass a ha W hW q hq hq1 t K hK.measurableSet hK.isBounded c hc
    (by rintro z ⟨w,hw,rfl⟩; exact hcK w hw) (upperExtension f)
    (upperExtension_measurable f) (upperExtension_bounded f) U hU]
  apply integral_congr_ae
  filter_upwards [] with b
  simp_rw [←upperExtension_apply f]
  trans ∫z in {z : ℂ | 0<z.im},upperExtension f z*remainingMassDensity a q t b z
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
    · rw [upperExtension_zero f z (by rintro ⟨w,hw,rfl⟩; exact hz w.2),zero_mul]
    · rw [upperExtension_zero f z hz,zero_mul]
  · exact (integral_subtype_comap (μ := (volume : Measure ℂ)) upperPlane_open.measurableSet
      (fun z : ℂ => upperExtension f z*remainingMassDensity a q t b z)).symm
end ExactSLEGreen
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction
open scoped Classical NNReal ENNReal Topology
lemma actualUpper_remaining_integral_tendsto (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℝ≥0) (f : C_c(UpperPlane,ℝ)) (U : Set ExactSLEGenerator.Driver)
    (q : ℕ → ℝ) (hq : ∀n,0<q n ∧ q n≤1) (hlim : Tendsto q atTop (𝓝 0)) :
    Tendsto (fun n => ∫b in U, (∫z : UpperPlane,f z*remainingMassDensity a (q n) t b z.1∂upperArea) ∂W)
      atTop (𝓝 (∫b in U, (∫z : UpperPlane,f z*survivingGreen a t b z.1∂upperArea) ∂W)) := by
  let K := tsupport f
  have hK : IsCompact K := f.hasCompactSupport
  have hfin : upperArea K<∞ := by
    rw [upperArea,upper_embedding.comap_apply]
    exact (hK.image continuous_subtype_val).measure_lt_top
  have : IsFiniteMeasure (upperArea.restrict K) := ⟨by simpa using hfin⟩
  obtain ⟨c,hc,hcK⟩ := upper_compact_lower K hK
  obtain ⟨B,hB,hBf⟩ := upperExtension_bounded f
  have H := actual_remaining_spatial_L1 a ha W hW t K hK.measurableSet hfin (c/2) (by positivity)
    (fun z hz => by have := hcK z hz; linarith) f f.continuous.measurable B hB
    (fun z hz => by simpa only [upperExtension_apply] using hBf z.1 ⟨z,hz,rfl⟩) q hq hlim
  let F : UpperPlane × ExactSLEGenerator.Driver → ℝ := fun p => f p.1*survivingGreen a t p.2 p.1.1
  let R : ℕ → UpperPlane × ExactSLEGenerator.Driver → ℝ := fun n p => f p.1*remainingMassDensity a (q n) t p.2 p.1.1
  let μ := (upperArea.restrict K).prod (W.restrict U)
  have hFi : Integrable F μ := H.1.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hRm (n : ℕ) : Measurable (R n) :=
    (f.continuous.measurable.comp measurable_fst).mul
      ((remainingMassDensity_measurable a ha (q n) (hq n).1 (hq n).2 t).comp
        (measurable_snd.prodMk (measurable_subtype_coe.comp measurable_fst)))
  have hbound (n : ℕ) (p : UpperPlane × ExactSLEGenerator.Driver) : ‖R n p‖≤‖F p‖ := by
    dsimp only [R,F]
    rw [norm_mul,norm_mul,Real.norm_of_nonneg (remainingMassDensity_nonneg _ _ _ _ _),
      Real.norm_of_nonneg (survivingGreen_nonneg _ _ _ _)]
    exact mul_le_mul_of_nonneg_left (remainingMassDensity_le_surviving _ _ _ _ _ p.1.2) (norm_nonneg _)
  have hRi (n : ℕ) : Integrable (R n) μ := hFi.norm.mono' (hRm n).aestronglyMeasurable
    (Eventually.of_forall (hbound n))
  have ht := tendsto_integral_of_dominated_convergence (fun p => ‖F p‖)
    (fun n => (hRm n).aestronglyMeasurable) hFi.norm (fun n => Eventually.of_forall (hbound n))
    (Eventually.of_forall (fun p => (remaining_to_surviving a ha t q hq hlim p.2 p.1.1 p.1.2).const_mul (f p.1)))
  have he (g : UpperPlane → ℝ) : (∫z in K,f z*g z∂upperArea) = ∫z,f z*g z∂upperArea :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by rw [image_eq_zero_of_notMem_tsupport hz,zero_mul])
  have hRint (n : ℕ) : (∫p,R n p∂μ) = ∫b in U,(∫z : UpperPlane,f z*remainingMassDensity a (q n) t b z.1∂upperArea)∂W := by
    rw [integral_prod_symm (R n) (hRi n)]
    apply integral_congr_ae
    filter_upwards [] with b
    exact he _
  have hFint : (∫p,F p∂μ) = ∫b in U,(∫z : UpperPlane,f z*survivingGreen a t b z.1∂upperArea)∂W := by
    rw [integral_prod_symm F hFi]
    apply integral_congr_ae
    filter_upwards [] with b
    exact he _
  change Tendsto (fun n => ∫p,R n p∂μ) atTop (𝓝 (∫p,F p∂μ)) at ht
  simpa only [hRint,hFint] using ht
end ExactSLEGreen
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction
open scoped Classical NNReal ENNReal Topology
lemma setIntegral_tendsto_of_L1 {Ω : Type*} [MeasurableSpace Ω] (W : Measure Ω)
    (F : ℕ → Ω → ℝ) (g : Ω → ℝ) (hF : ∀n,Integrable (F n) W) (hg : Integrable g W)
    (hlim : Tendsto (fun n => eLpNorm (fun b => F n b-g b) 1 W) atTop (𝓝 0)) (U : Set Ω) :
    Tendsto (fun n => ∫b in U,F n b∂W) atTop (𝓝 (∫b in U,g b∂W)) := by
  have hsmall : Tendsto (fun n => eLpNorm (fun b => F n b-g b) 1 (W.restrict U)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall (fun _ => bot_le))
      (Eventually.of_forall (fun n => eLpNorm_mono_measure _ Measure.restrict_le_self))
  exact tendsto_integral_of_L1 g hg.integrableOn.aestronglyMeasurable
    (Eventually.of_forall (fun n => (hF n).integrableOn))
    (hsmall.congr fun index => eLpNorm_one_eq_lintegral_enorm
      ((hF index).integrableOn.aestronglyMeasurable.sub hg.integrableOn.aestronglyMeasurable))
lemma scalar_convex_tail_limit (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
    (hs : ∀k j,j∈s k→k≤j) (hc : ∀k j,j∈s k→0≤c k j) (hsum : ∀k,∑j∈s k,c k j=1)
    (x : ℕ → ℝ) (L : ℝ) (hx : Tendsto x atTop (𝓝 L)) :
    Tendsto (fun k => ∑j∈s k,c k j*x j) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at hx ⊢
  intro ε hε
  obtain ⟨N,hN⟩ := hx (ε/2) (by positivity)
  refine ⟨N,fun k hk => ?_⟩
  rw [Real.dist_eq]
  have he : (∑j∈s k,c k j*x j)-L = ∑j∈s k,c k j*(x j-L) := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hsum k,one_mul]
  rw [he]
  calc
    |∑j∈s k,c k j*(x j-L)| ≤ ∑j∈s k,|c k j*(x j-L)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑j∈s k,c k j*(ε/2) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul,abs_of_nonneg (hc k j hj)]
      exact mul_le_mul_of_nonneg_left (by simpa [Real.dist_eq] using (hN j (hk.trans (hs k j hj))).le) (hc k j hj)
    _ = ε/2 := by rw [←Finset.sum_mul,hsum k,one_mul]
    _ < ε := by linarith
end ExactSLEGreen
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction
open scoped Classical NNReal ENNReal
theorem actual_radon_compact_conditional (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ)
      (μ : ExactSLEGenerator.Driver → ℕ → Measure UpperPlane),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k j, j∈s k → 0≤coeff k j) ∧
      (∀ k, ∑ j∈s k, coeff k j=1) ∧
      (∀ b i, IsFiniteMeasureOnCompacts (μ b i) ∧ (μ b i).Regular) ∧
      (∀ i (f : C_c(UpperPlane, ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ b i) (m : ℝ≥0∞) W) ∧
      (∀ i (f : C_c(UpperPlane, ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k, coeff k j *
            ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            - ∫z,f z∂μ b i) 1 W) atTop (𝓝 0)) ∧
      (∀ i, t i=∞ → ∀ f : C_c(UpperPlane,ℝ),
        (∫b, (∫z,f z∂μ b i) ∂W) = ∫z : UpperPlane,
          f z * (Real.exp (-alpha a*Real.log 2)*physicalGreen a (z.1,0)) ∂upperArea) ∧
      (∀ i (t₀ : ℝ≥0), t i=t₀ → ∀ f : C_c(UpperPlane,ℝ),
        AEStronglyMeasurable[rawFiltration t₀] (fun b => ∫z,f z∂μ b i) W) ∧
      (∀ i j (t₀ : ℝ≥0), t i=t₀ → t j=∞ → ∀ f : C_c(UpperPlane,ℝ),
        ∀ U : Set ExactSLEGenerator.Driver, MeasurableSet[rawFiltration t₀] U →
        (∫b in U, (∫z,f z∂μ b j)-(∫z,f z∂μ b i) ∂W) =
          ∫b in U, (∫z : UpperPlane,f z*survivingGreen a t₀ b z.1 ∂upperArea) ∂W) ∧
      ∀ᵐ b ∂W,
        (∀ i j, t i ≤ t j → μ b i ≤ μ b j) ∧
        (∀ i (f : C_c(UpperPlane, ℝ)),
          Tendsto (fun k => ∑ j∈s k, coeff k j *
            ∫ z, f z ∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫ z, f z ∂μ b i)))
 := by
  obtain ⟨s,c,μ,hs,hc,hsum,hμ,hmom,hL1,hmean,hraw,h⟩ := actual_radon_raw_evaluations a ha W hW t
  refine ⟨s,c,μ,hs,hc,hsum,hμ,hmom,hL1,hmean,hraw,?_,h⟩
  intro i j t₀ hi hj f U hU
  let q : ℕ → ℝ := fun n => Real.exp (-2*a*((n:ℝ)+1))
  have hq (n : ℕ) : 0<q n ∧ q n≤1 := by
    refine ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr ?_⟩
    have hn : (0:ℝ)≤n := Nat.cast_nonneg _
    have ha0 : 0<a := by linarith
    nlinarith
  have hqlim : Tendsto q atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    apply Tendsto.const_mul_atTop_of_neg (by linarith : -2*a<0)
    apply Filter.tendsto_atTop.mpr
    intro B
    filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually (eventually_ge_atTop B)] with n hn
    linarith
  let F : ℕ → ℕ → ExactSLEGenerator.Driver → ℝ := fun l k b =>
    ∑ n∈s k,c k n*∫z,f z∂actualUpperMass a (q n) (t l) b
  obtain ⟨C,hC,hCb⟩ := actualUpperMass_Lp_bound a ha W hW 1 (by norm_num) f
  have hEval (n : ℕ) (v : ℝ≥0∞) : Integrable (fun b => ∫z,f z∂actualUpperMass a (q n) v b) W :=
    (hCb (q n) (hq n).1 (hq n).2 v).1.integrable (by norm_num)
  have hFi (l k : ℕ) : Integrable (F l k) W :=
    integrable_finsetSum (s k) (fun n hn => (hEval n (t l)).const_mul (c k n))
  have hμi (l : ℕ) : Integrable (fun b => ∫z,f z∂μ b l) W :=
    (hmom l f 1).integrable (by norm_num)
  have hlim (l : ℕ) := setIntegral_tendsto_of_L1 W (F l) (fun b => ∫z,f z∂μ b l)
    (hFi l) (hμi l) (hL1 l f) U
  let R : ℕ → ℝ := fun n => ∫b in U,(∫z : UpperPlane,f z*remainingMassDensity a (q n) t₀ b z.1∂upperArea)∂W
  let L : ℝ := ∫b in U,(∫z : UpperPlane,f z*survivingGreen a t₀ b z.1∂upperArea)∂W
  have hRlim : Tendsto R atTop (𝓝 L) := actualUpper_remaining_integral_tendsto a ha W hW t₀ f U q hq hqlim
  have hcombo := scalar_convex_tail_limit s c hs hc hsum R L hRlim
  have he (k : ℕ) : (∫b in U,F j k b∂W)-(∫b in U,F i k b∂W) = ∑n∈s k,c k n*R n := by
    dsimp only [F]
    rw [integral_finsetSum _ (fun n hn => ((hEval n (t j)).const_mul (c k n)).integrableOn),
      integral_finsetSum _ (fun n hn => ((hEval n (t i)).const_mul (c k n)).integrableOn)]
    simp only [integral_const_mul]
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [←mul_sub,←integral_sub (hEval n (t j)).integrableOn (hEval n (t i)).integrableOn]
    rw [hj,hi,actualUpperMass_finite_kernel a ha W hW (q n) (hq n).1 (hq n).2 t₀ f U hU]
  rw [integral_sub (hμi j).integrableOn (hμi i).integrableOn]
  exact tendsto_nhds_unique ((hlim j).sub (hlim i)) (by simpa only [he] using hcombo)
end ExactSLEGreen
end
end

end OAI
