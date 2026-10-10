import Mathlib
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Brownian Support estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BrownianSupport
open BrownianPredictable

lemma preBrownian_past_square_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[pastSigma B s] A) :
    (∫ sample in A, (B s sample)^2 ∂P) ≤ ∫ sample in A, (B t sample)^2 ∂P := by
  have hraw : pastSigma B s ≤ ‹MeasurableSpace Ω› :=
    (Measurable.of_eval (fun time : Set.Iic s => hBm time)).comap_le
  have hAm : MeasurableSet A := hraw _ hA
  have hs := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have ht := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hi : IndepFun (A.indicator (B s)) (fun sample => B t sample-B s sample) P := by
    have hall := (hB.indepFun_shift s).symm
    have hX : Measurable[pastSigma B s] (A.indicator (B s)) :=
      (past_measurable_eval B le_rfl).indicator hA
    have hf := hall.comp measurable_id (measurable_pi_apply (t-s))
    simp only [Function.comp_def,id_eq,add_tsub_cancel_of_le hst] at hf
    exact indep_of_indep_of_le_left hf hX.comap_le
  have hz : (∫ sample in A, B s sample*(B t sample-B s sample) ∂P) = 0 := by
    have he := hi.integral_fun_mul_eq_mul_integral
      ((hBm s).indicator hAm).aestronglyMeasurable ((hBm t).sub (hBm s)).aestronglyMeasurable
    have hind : (fun sample => A.indicator (B s) sample*(B t sample-B s sample)) =
        A.indicator (fun sample => B s sample*(B t sample-B s sample)) := by
      funext sample
      by_cases ha : sample ∈ A <;> simp [ha]
    rw [hind,integral_indicator hAm,integral_sub (hB.integrable_eval t) (hB.integrable_eval s),
      hB.integral_eval t,hB.integral_eval s,sub_self,mul_zero] at he
    exact he
  have hcross : Integrable (fun sample => B s sample*(B t sample-B s sample)) P :=
    hs.integrable_mul (ht.sub hs)
  have his : Integrable (fun sample => (B s sample)^2) P := hs.integrable_sq
  have hid : Integrable (fun sample => (B t sample-B s sample)^2) P := (ht.sub hs).integrable_sq
  have he : (∫ sample in A, (B t sample)^2 ∂P) =
      (∫ sample in A, (B s sample)^2 ∂P) + ∫ sample in A, (B t sample-B s sample)^2 ∂P := by
    calc
      _ = ∫ sample in A, ((B s sample)^2+2*(B s sample*(B t sample-B s sample)))+
          (B t sample-B s sample)^2 ∂P := integral_congr_ae (Eventually.of_forall (fun _ => by ring))
      _ = (∫ sample in A, (B s sample)^2+2*(B s sample*(B t sample-B s sample)) ∂P) +
          ∫ sample in A, (B t sample-B s sample)^2 ∂P :=
        integral_add ((his.restrict (s := A)).add ((hcross.restrict (s := A)).const_mul 2)) (hid.restrict (s := A))
      _ = ((∫ sample in A, (B s sample)^2 ∂P) +
          2*(∫ sample in A, B s sample*(B t sample-B s sample) ∂P)) +
          ∫ sample in A, (B t sample-B s sample)^2 ∂P := by
        congr 1
        calc
          _ = (∫ sample in A, (B s sample)^2 ∂P) +
              ∫ sample in A, 2*(B s sample*(B t sample-B s sample)) ∂P :=
            integral_add (his.restrict (s := A)) ((hcross.restrict (s := A)).const_mul 2)
          _ = _ := by rw [integral_const_mul]
      _ = _ := by rw [hz,mul_zero,add_zero]
  rw [he]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

lemma preBrownian_square_submartingale {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (t : ℕ → ℝ≥0) (ht : Monotone t) :
    let F : Filtration ℕ ‹MeasurableSpace Ω› :=
      ⟨fun n => pastSigma B (t n),fun _ _ hij => pastSigma_mono B (ht hij),
        fun n => (Measurable.of_eval (fun time : Set.Iic (t n) => hBm time)).comap_le⟩
    Submartingale (fun n sample => (B (t n) sample)^2) F P := by
  intro F
  apply submartingale_of_setIntegral_le
  · intro n
    exact ((past_measurable_eval B le_rfl).pow_const 2).stronglyMeasurable
  · intro n
    exact (hB.isGaussianProcess.hasGaussianLaw_eval (t n)).memLp_two.integrable_sq
  · intro i j hij A hA
    exact preBrownian_past_square_le hB hBm (ht hij) hA

lemma preBrownian_finite_max_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) {a : ℝ} (ha : 0 < a) :
    P {sample | ∃ i ≤ n, a ≤ |B (t i) sample|} ≤ ENNReal.ofReal ((t n:ℝ)/a^2) := by
  let f : ℕ → Ω → ℝ := fun n sample => (B (t n) sample)^2
  have hm := maximal_ineq (preBrownian_square_submartingale hB hBm t ht)
    (show 0 ≤ f from fun _ _ => sq_nonneg _) (ε := (a^2).toNNReal) n
  simp only [Real.coe_toNNReal _ (sq_nonneg a)] at hm
  have he : {sample | (a^2) ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one (fun k => f k sample)} =
      {sample | ∃ i ≤ n, a ≤ |B (t i) sample|} := by
    ext sample
    simp only [mem_ofPred_eq,Finset.le_sup'_iff,Finset.mem_range,Nat.lt_succ_iff,f]
    constructor
    · rintro ⟨i,hi,hv⟩
      exact ⟨i,hi,(sq_le_sq₀ ha.le (abs_nonneg _)).1 (by simpa using hv)⟩
    · rintro ⟨i,hi,hv⟩
      exact ⟨i,hi,by simpa using (sq_le_sq₀ ha.le (abs_nonneg _)).2 hv⟩
  change ENNReal.ofReal (a^2) * P _ ≤ _ at hm
  rw [he] at hm
  have hi : (∫ sample in {sample | ∃ i ≤ n, a ≤ |B (t i) sample|}, (B (t n) sample)^2 ∂P) ≤ (t n:ℝ) := by
    calc
      _ ≤ ∫ sample, (B (t n) sample)^2 ∂P := integral_mono_measure Measure.restrict_le_self
        (Eventually.of_forall (fun _ => sq_nonneg _))
        (hB.isGaussianProcess.hasGaussianLaw_eval (t n)).memLp_two.integrable_sq
      _ = _ := ((hB.hasLaw_eval (t n)).integral_comp
        (show AEStronglyMeasurable (fun x : ℝ => x^2) _ from by fun_prop)).trans
          (BrownianPredictable.gaussian_second_moment _)
  have hh := hm.trans (ENNReal.ofReal_le_ofReal hi)
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos ha)]
  exact (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt (ENNReal.ofReal_pos.2 (sq_pos_of_pos ha)))) (Or.inl ENNReal.ofReal_ne_top)).2 (by simpa [mul_comm] using hh)

end SLEExactGauge.BrownianSupport

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BrownianPredictable

def restartIndex {Ω : Type*} (τ : Ω → ℝ≥0) (n : ℕ) (sample : Ω) : ℕ :=
  Nat.ceil (τ sample*((n:ℝ≥0)+1))

def restartGrid (n k : ℕ) : ℝ≥0 := (k:ℝ≥0)/((n:ℝ≥0)+1)

def restartTime {Ω : Type*} (τ : Ω → ℝ≥0) (n : ℕ) (sample : Ω) : ℝ≥0 :=
  restartGrid n (restartIndex τ n sample)

lemma restartIndex_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {τ : Ω → ℝ≥0} (hτ : AEMeasurable τ P) (n : ℕ) : AEMeasurable (restartIndex τ n) P :=
  Nat.measurable_ceil.comp_aemeasurable (hτ.mul_const _)

lemma restartTime_bounds {Ω : Type*} (τ : Ω → ℝ≥0) (n : ℕ) (sample : Ω) :
    τ sample ≤ restartTime τ n sample ∧
      restartTime τ n sample ≤ τ sample+1/((n:ℝ≥0)+1) := by
  have ha : 0 < (n:ℝ≥0)+1 := by positivity
  constructor
  · exact (le_div_iff₀ ha).2 (Nat.le_ceil _)
  · change (Nat.ceil (τ sample*((n:ℝ≥0)+1)):ℝ≥0)/((n:ℝ≥0)+1) ≤ _
    apply le_of_lt
    calc
      _ < (τ sample*((n:ℝ≥0)+1)+1)/((n:ℝ≥0)+1) :=
        (div_lt_div_iff_of_pos_right ha).2 (Nat.ceil_lt_add_one (by positivity))
      _ = _ := by rw [add_div,mul_div_cancel_right₀ _ ha.ne']

lemma restartTime_tendsto {Ω : Type*} (τ : Ω → ℝ≥0) (sample : Ω) :
    Tendsto (fun n => restartTime τ n sample) atTop (𝓝 (τ sample)) := by
  have hh : Tendsto (fun n : ℕ => τ sample+1/((n:ℝ≥0)+1)) atTop (𝓝 (τ sample)) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
    (fun n => (restartTime_bounds τ n sample).1) (fun n => (restartTime_bounds τ n sample).2)

lemma restartIndex_past {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hstop : ∀ t : ℝ≥0, MeasurableSet[pastSigma B t] (A ∩ {sample | τ sample ≤ t}))
    (n k : ℕ) : MeasurableSet[pastSigma B (restartGrid n k)]
      (A ∩ {sample | restartIndex τ n sample = k}) := by
  have ha : 0 < (n:ℝ≥0)+1 := by positivity
  by_cases hk : k=0
  · subst k
    have he : A ∩ {sample | restartIndex τ n sample = 0} = A ∩ {sample | τ sample ≤ 0} := by
      ext sample
      simp only [mem_inter_iff,mem_ofPred_eq,restartIndex,Nat.ceil_eq_zero]
      constructor
      · rintro ⟨hA,ht⟩
        exact ⟨hA,(mul_le_mul_iff_left₀ ha).1 (by simpa using ht)⟩
      · rintro ⟨hA,ht⟩
        exact ⟨hA,mul_nonpos_of_nonpos_of_nonneg ht ha.le⟩
    rw [he]
    have hz : restartGrid n 0 = 0 := by simp [restartGrid]
    rw [hz]
    exact hstop 0
  · have hle : restartGrid n (k-1) ≤ restartGrid n k := by
      apply div_le_div_of_nonneg_right _ ha.le
      exact_mod_cast Nat.sub_le k 1
    have hprev : MeasurableSet[pastSigma B (restartGrid n k)]
        (A ∩ {sample | τ sample ≤ restartGrid n (k-1)}) :=
      (pastSigma_mono B hle) _ (hstop _)
    have he : A ∩ {sample | restartIndex τ n sample = k} =
        (A ∩ {sample | τ sample ≤ restartGrid n k}) \
          (A ∩ {sample | τ sample ≤ restartGrid n (k-1)}) := by
      ext sample
      simp only [mem_inter_iff,mem_ofPred_eq,Set.mem_sdiff,restartIndex,Nat.ceil_eq_iff hk,
        restartGrid,le_div_iff₀ ha,not_and,not_le]
      constructor
      · rintro ⟨hA,hl,hu⟩
        exact ⟨⟨hA,hu⟩,fun _ => hl⟩
      · rintro ⟨⟨hA,hu⟩,hl⟩
        exact ⟨hA,hl hA,hu⟩
    rw [he]
    exact (hstop _).diff hprev

end SLEExactGauge.BrownianPredictable

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BrownianSupport
open BrownianPredictable

lemma brownian_finite_max_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (n : ℕ) {a : ℝ} (ha : 0 < a) :
    P {sample | ∃ i ≤ n, a ≤ |B (t i) sample|} ≤ ENNReal.ofReal ((t n:ℝ)/a^2) := by
  let C : ℝ≥0 → Ω → ℝ := fun t => (hB.aemeasurable t).mk (B t)
  have hm (t : ℝ≥0) : Measurable (C t) := (hB.aemeasurable t).measurable_mk
  have he (t : ℝ≥0) : B t =ᵐ[P] C t := (hB.aemeasurable t).ae_eq_mk
  have hC : IsPreBrownianReal C P := hB.congr he
  have hmeasure : P {sample | ∃ i ≤ n, a ≤ |B (t i) sample|} =
      P {sample | ∃ i ≤ n, a ≤ |C (t i) sample|} := by
    apply measure_congr
    filter_upwards [ae_all_iff.2 (fun i : ℕ => he (t i))] with sample hh
    apply propext
    simp only [hh]
  rw [hmeasure]
  exact preBrownian_finite_max_bound hC hm t ht n ha

lemma brownian_oscillation_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P {sample | ∃ t ∈ Icc 0 T, a < |B t sample|} ≤ ENNReal.ofReal ((T:ℝ)/a^2) := by
  let grid (n i : ℕ) : ℝ≥0 := min T (restartGrid n i)
  let N (n : ℕ) := Nat.ceil (T*((n:ℝ≥0)+1))
  let E (n : ℕ) : Set Ω := {sample | ∃ i ≤ N n, a ≤ |B (grid n i) sample|}
  have hgrid (n : ℕ) : Monotone (grid n) := by
    intro i j hij
    apply min_le_min le_rfl
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have hend (n : ℕ) : grid n (N n) = T := by
    apply min_eq_left
    exact (restartTime_bounds (fun _ : Unit => T) n ()).1
  have hE (n : ℕ) : P (E n) ≤ ENNReal.ofReal ((T:ℝ)/a^2) := by
    have hh := brownian_finite_max_bound hB.toIsPreBrownianReal (grid n) (hgrid n) (N n) ha
    simpa only [hend] using hh
  let F (k : ℕ) : Set Ω := ⋂ n ≥ k, E n
  have hd : Monotone F := by
    intro k l hkl sample hs
    simp only [F,mem_iInter] at hs ⊢
    exact fun n hn => hs n (hkl.trans hn)
  have hsub : {sample | ∃ t ∈ Icc 0 T, a < |B t sample|} ≤ᵐ[P] ⋃ k, F k := by
    filter_upwards [hB.cont] with sample hc hs
    rcases hs with ⟨t,ht,haB⟩
    have htend : Tendsto (fun n => min T (restartTime (fun _ : Unit => t) n ())) atTop (𝓝 t) := by
      have hh := (tendsto_const_nhds (x := T)).min (restartTime_tendsto (fun _ : Unit => t) ())
      simpa only [min_eq_right ht.2] using hh
    have hev := ((hc.continuousAt.tendsto.comp htend).abs).eventually (lt_mem_nhds haB)
    obtain ⟨k,hk⟩ := eventually_atTop.1 hev
    apply mem_iUnion.2
    refine ⟨k,?_⟩
    simp only [F,mem_iInter]
    intro n hn
    refine ⟨restartIndex (fun _ : Unit => t) n (),?_,(hk n hn).le⟩
    apply Nat.ceil_mono
    exact mul_le_mul_of_nonneg_right ht.2 (by positivity)
  calc
    _ ≤ P (⋃ k, F k) := measure_mono_ae hsub
    _ = ⨆ k, P (F k) := hd.directed_le.measure_iUnion
    _ ≤ _ := iSup_le (fun k => (measure_mono (by
      intro sample hs
      exact mem_iInter.1 (mem_iInter.1 hs k) le_rfl)).trans (hE k))

end SLEExactGauge.BrownianSupport

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BrownianSupport

private def densityFloor : ℝ := (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(1/2:ℝ))

private lemma densityFloor_pos : 0 < densityFloor := by
  dsimp [densityFloor]
  positivity

private lemma gaussian_pdf_lower {v : ℝ≥0} (hv : 0 < v) {x : ℝ} (hx : |x| ≤ Real.sqrt v) :
    densityFloor / Real.sqrt v ≤ gaussianPDFReal 0 v x := by
  have hvR : 0 < (v:ℝ) := hv
  have hs : 0 < Real.sqrt (v:ℝ) := Real.sqrt_pos.2 hvR
  have hx2 : x^2 ≤ (v:ℝ) := by
    have hh := (sq_le_sq₀ (abs_nonneg x) hs.le).2 hx
    simpa only [sq_abs,Real.sq_sqrt hvR.le] using hh
  have he : -(1/2:ℝ) ≤ -x^2/(2*(v:ℝ)) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  calc
    _ = (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹ * Real.exp (-(1/2:ℝ)) := by
      rw [Real.sqrt_mul (by positivity)]
      dsimp [densityFloor]
      field_simp
    _ ≤ _ := by
      change _ ≤ (Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹ * Real.exp (-(x-0)^2/(2*(v:ℝ)))
      simp only [sub_zero]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 he) (by positivity)

lemma gaussian_short_interval_lower {v : ℝ≥0} (hv : 0 < v) {c α L : ℝ}
    (hα : 0 < α) (hc : |c| ≤ L*(v:ℝ))
    (hsmall : (L+α)*(v:ℝ) ≤ Real.sqrt v) :
    ENNReal.ofReal (2*densityFloor*α*Real.sqrt v) ≤
      gaussianReal 0 v {x : ℝ | |x-c| < α*(v:ℝ)} := by
  have hvR : 0 < (v:ℝ) := hv
  have hs : 0 < Real.sqrt (v:ℝ) := Real.sqrt_pos.2 hvR
  let A : Set ℝ := Ioo (c-α*(v:ℝ)) (c+α*(v:ℝ))
  have hA : {x : ℝ | |x-c| < α*(v:ℝ)} = A := by
    ext x
    simp only [mem_ofPred_eq,A,mem_Ioo,abs_lt]
    constructor <;> intro hh <;> constructor <;> linarith [hh.1,hh.2]
  rw [hA,gaussianReal_apply_eq_integral 0 hv.ne']
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ∫ x in A, densityFloor/Real.sqrt v := by
      rw [setIntegral_const]
      simp only [smul_eq_mul,A,Real.volume_real_Ioo]
      rw [max_eq_left (by nlinarith [mul_pos hα hvR] : 0 ≤ c+α*(v:ℝ)-(c-α*(v:ℝ)))]
      field_simp
      rw [Real.sq_sqrt hvR.le]
      ring
    _ ≤ _ := by
      apply setIntegral_mono_on (integrable_const _) (integrable_gaussianPDFReal 0 v).integrableOn measurableSet_Ioo
      intro x hx
      apply gaussian_pdf_lower hv
      have hxc : |x-c| < α*(v:ℝ) := by
        have hh : x ∈ {x : ℝ | |x-c| < α*(v:ℝ)} := hA.symm ▸ hx
        exact hh
      calc
        |x| ≤ |x-c|+|c| := by simpa using abs_add_le (x-c) c
        _ ≤ (L+α)*(v:ℝ) := by nlinarith
        _ ≤ _ := hsmall

lemma short_endpoint_dominates {L α b : ℝ} (hL : 0 ≤ L) (hα : 0 < α) (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (v : ℝ≥0), 0 < v → (v:ℝ) ≤ δ → ∀ c : ℝ,
      |c| ≤ L*(v:ℝ) → ENNReal.ofReal ((v:ℝ)/b^2) <
        gaussianReal 0 v {x : ℝ | |x-c| < α*(v:ℝ)} := by
  let r : ℝ := min (1/(L+α+1)) (densityFloor*α*b^2)
  have hr : 0 < r := lt_min (by positivity) (by positivity [densityFloor_pos])
  refine ⟨r^2,by positivity,fun v hv hvr c hc => ?_⟩
  have hvR : 0 < (v:ℝ) := hv
  have hs : 0 < Real.sqrt (v:ℝ) := Real.sqrt_pos.2 hvR
  have hsr : Real.sqrt (v:ℝ) ≤ r := (Real.sqrt_le_iff).2 ⟨hr.le,hvr⟩
  have hsmall : (L+α)*(v:ℝ) ≤ Real.sqrt v := by
    have hr1 : r ≤ 1/(L+α+1) := min_le_left _ _
    have hh : (L+α+1)*Real.sqrt (v:ℝ) ≤ 1 := by
      have hc' := (le_div_iff₀ (by positivity : 0 < L+α+1)).1 (hsr.trans hr1)
      nlinarith
    nlinarith [Real.sq_sqrt hvR.le]
  apply lt_of_lt_of_le _ (gaussian_short_interval_lower hv hα hc hsmall)
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity [densityFloor_pos])).2
  apply (div_lt_iff₀ (sq_pos_of_pos hb)).2
  have hr2 : r ≤ densityFloor*α*b^2 := min_le_right _ _
  have hh := hsr.trans hr2
  have hmul := mul_le_mul_of_nonneg_left hh hs.le
  nlinarith [Real.sq_sqrt hvR.le,densityFloor_pos]

end SLEExactGauge.BrownianSupport

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BrownianSupport
open BrownianPredictable

def probeTime (T : ℝ≥0) (q : I) : ℝ≥0 := T * ⟨q,q.property.1⟩

lemma probeTime_le (T : ℝ≥0) (q : I) : probeTime T q ≤ T := by
  change (T:ℝ)*(q:ℝ) ≤ T
  simpa using mul_le_mul_of_nonneg_left q.property.2 T.coe_nonneg

lemma continuous_probeTime (T : ℝ≥0) : Continuous (probeTime T) := by
  apply Continuous.const_mul
  exact continuous_subtype_val.subtype_mk (fun q => q.property.1)

def stepSet (h : ℝ≥0) (c α b : ℝ) : Set (ℝ≥0 → ℝ) :=
  {f | |f h-c| < α*(h:ℝ) ∧ ∀ n : ℕ, |f (probeTime h (denseSeq I n))| ≤ b}

lemma measurableSet_stepSet (h : ℝ≥0) (c α b : ℝ) : MeasurableSet (stepSet h c α b) := by
  change MeasurableSet ({f : ℝ≥0 → ℝ | |f h-c| < α*(h:ℝ)} ∩
    {f : ℝ≥0 → ℝ | ∀ n : ℕ, |f (probeTime h (denseSeq I n))| ≤ b})
  apply MeasurableSet.inter
  · exact measurableSet_lt (((measurable_pi_apply h : Measurable (fun f : ℝ≥0 → ℝ => f h))).sub_const c).abs measurable_const
  · simp only [ofPred_forall]
    exact MeasurableSet.iInter fun n => measurableSet_le (measurable_pi_apply _).abs measurable_const

lemma probe_bound_all {f : ℝ≥0 → ℝ} (hf : Continuous f) (T : ℝ≥0) {b : ℝ}
    (hb : ∀ n : ℕ, |f (probeTime T (denseSeq I n))| ≤ b) :
    ∀ t ≤ T, |f t| ≤ b := by
  have hall (q : I) : |f (probeTime T q)| ≤ b :=
    (denseRange_denseSeq I).induction_on q
      (isClosed_le ((hf.comp (continuous_probeTime T)).abs) continuous_const) hb
  intro t ht
  by_cases hT : T=0
  · have ht0 : t=0 := le_antisymm (ht.trans hT.le) (bot_le)
    have hz : probeTime T (0:I) = 0 := by
      apply NNReal.coe_injective
      change (T:ℝ)*(0:ℝ) = (0:ℝ)
      exact mul_zero _
    simpa only [ht0,hz] using hall (0:I)
  · have hTp : 0 < (T:ℝ) := by exact_mod_cast lt_of_le_of_ne (bot_le : 0 ≤ T) (Ne.symm hT)
    let q : I := ⟨(t:ℝ)/(T:ℝ),⟨div_nonneg t.coe_nonneg T.coe_nonneg,(div_le_one hTp).2 ht⟩⟩
    have he : probeTime T q = t := by
      apply NNReal.coe_injective
      change (T:ℝ)*((t:ℝ)/(T:ℝ)) = t
      field_simp
    simpa only [he] using hall q

def stepEvent {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (t h : ℝ≥0) (c α b : ℝ) : Set Ω :=
  (fun sample s => B (t+s) sample-B t sample) ⁻¹' stepSet h c α b

lemma stepEvent_past {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (t h : ℝ≥0) (c α b : ℝ) : MeasurableSet[pastSigma B (t+h)] (stepEvent B t h c α b) := by
  let : MeasurableSpace Ω := pastSigma B (t+h)
  change MeasurableSet[pastSigma B (t+h)]
    ({sample | |B (t+h) sample-B t sample-c| < α*(h:ℝ)} ∩
     {sample | ∀ n : ℕ, |B (t+probeTime h (denseSeq I n)) sample-B t sample| ≤ b})
  apply MeasurableSet.inter
  · apply measurableSet_lt _ measurable_const
    exact (((past_measurable_eval B (s:=t+h) (t:=t+h) le_rfl).sub
      (past_measurable_eval B (s:=t) (t:=t+h) (le_add_right le_rfl))).sub_const c).abs
  · simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    apply measurableSet_le _ measurable_const
    exact ((past_measurable_eval B (s:=t+probeTime h _) (t:=t+h) (by gcongr; exact probeTime_le h _)).sub
      (past_measurable_eval B (s:=t) (t:=t+h) (le_add_right le_rfl))).abs

lemma small_step_pos {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) {L α b : ℝ} (hL : 0 ≤ L) (hα : 0 < α) (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (h : ℝ≥0), 0 < h → (h:ℝ) ≤ δ → ∀ c : ℝ,
      |c| ≤ L*(h:ℝ) → ∀ t : ℝ≥0, 0 < P (stepEvent B t h c α b) := by
  obtain ⟨δ,hδ,hdom⟩ := short_endpoint_dominates hL hα hb
  refine ⟨δ,hδ,fun h hh hhδ c hc t => ?_⟩
  let C : ℝ≥0 → Ω → ℝ := fun s sample => B (t+s) sample-B t sample
  have hC : IsBrownianReal C P := hB.shift t
  let E : Set Ω := {sample | |C h sample-c| < α*(h:ℝ)}
  let Bad : Set Ω := {sample | ∃ s ∈ Icc 0 h, b < |C s sample|}
  have hE : P E = gaussianReal 0 h {x : ℝ | |x-c| < α*(h:ℝ)} :=
    (hC.toIsPreBrownianReal.hasLaw_eval h).measure_eq
      (p := fun x : ℝ => |x-c| < α*(h:ℝ))
      (measurableSet_lt (measurable_id.sub_const c).abs measurable_const)
  have hbad : P Bad < P E := by
    rw [hE]
    exact (brownian_oscillation_bound hC h hb).trans_lt (hdom h hh hhδ c hc)
  have hsub : E ⊆ stepEvent B t h c α b ∪ Bad := by
    intro sample hs
    by_cases hbad : sample ∈ Bad
    · exact Or.inr hbad
    · apply Or.inl
      refine ⟨hs,fun n => ?_⟩
      apply le_of_not_gt
      intro hn
      exact hbad ⟨probeTime h (denseSeq I n),⟨bot_le,probeTime_le h _⟩,hn⟩
  apply pos_iff_ne_zero.2
  intro hz
  have hm := (measure_mono (μ:=P) hsub).trans (measure_union_le _ _)
  rw [hz,zero_add] at hm
  exact (not_le_of_gt hbad) hm

lemma past_inter_step {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (t h : ℝ≥0) (c α b : ℝ) (A : Set Ω) (hA : MeasurableSet[pastSigma B t] A) :
    P (A ∩ stepEvent B t h c α b) = P A * P (stepEvent B t h c α b) := by
  have hi := (hB.toIsPreBrownianReal.indepFun_shift t).symm
  apply hi.meas_inter hA
  exact (measurableSet_stepSet h c α b).preimage (comap_measurable _)

def stepsEvent {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (c : ℕ → ℝ)
    (α b : ℝ) (n : ℕ) : Set Ω :=
  {sample | ∀ i < n, sample ∈ stepEvent B ((i:ℝ≥0)*h) h (c i) α b}

lemma stepsEvent_zero {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (c : ℕ → ℝ)
    (α b : ℝ) : stepsEvent B h c α b 0 = univ := by
  ext sample
  simp [stepsEvent]

lemma stepsEvent_succ {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (c : ℕ → ℝ)
    (α b : ℝ) (n : ℕ) : stepsEvent B h c α b (n+1) =
      stepsEvent B h c α b n ∩ stepEvent B ((n:ℝ≥0)*h) h (c n) α b := by
  ext sample
  simp only [stepsEvent,mem_ofPred_eq,mem_inter_iff,Nat.lt_succ_iff]
  exact ⟨fun hh => ⟨fun i hi => hh i (Nat.le_of_lt hi),hh n le_rfl⟩,
    fun hh i hi => (lt_or_eq_of_le hi).elim (hh.1 i) (fun he => he ▸ hh.2)⟩

lemma stepsEvent_past {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (h : ℝ≥0) (c : ℕ → ℝ) (α b : ℝ) (n : ℕ) :
    MeasurableSet[pastSigma B ((n:ℝ≥0)*h)] (stepsEvent B h c α b n) := by
  induction n with
  | zero => rw [stepsEvent_zero]; exact .univ
  | succ n ih =>
    rw [stepsEvent_succ]
    have he : ((n+1:ℕ):ℝ≥0)*h = (n:ℝ≥0)*h+h := by push_cast; ring
    rw [he]
    exact ((pastSigma_mono B (s := (n:ℝ≥0)*h) (t := (n:ℝ≥0)*h+h) (le_add_right le_rfl)) _ ih).inter
      (stepEvent_past B _ _ _ _ _)

lemma stepsEvent_pos {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (h : ℝ≥0) (c : ℕ → ℝ) (α b : ℝ) (n : ℕ)
    (hpos : ∀ i < n, 0 < P (stepEvent B ((i:ℝ≥0)*h) h (c i) α b)) :
    0 < P (stepsEvent B h c α b n) := by
  induction n with
  | zero => rw [stepsEvent_zero,measure_univ]; exact zero_lt_one
  | succ n ih =>
    rw [stepsEvent_succ,past_inter_step hB _ _ _ _ _ _ (stepsEvent_past B h c α b n)]
    exact ENNReal.mul_pos (ih (fun i hi => hpos i (Nat.lt_succ_of_lt hi))).ne' (hpos n (Nat.lt_succ_self n)).ne'

lemma exists_grid_interval (h : ℝ≥0) {n : ℕ} (hn : 0 < n) {t : ℝ≥0}
    (ht : t ≤ (n:ℝ≥0)*h) :
    ∃ i < n, (i:ℝ≥0)*h ≤ t ∧ t ≤ ((i+1:ℕ):ℝ≥0)*h := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n=0
    · subst n
      exact ⟨0,by omega,by simp,by simpa using ht⟩
    · by_cases hh : t ≤ (n:ℝ≥0)*h
      · obtain ⟨i,hi,hi1,hi2⟩ := ih (Nat.pos_of_ne_zero hn0) hh
        exact ⟨i,Nat.lt_succ_of_lt hi,hi1,hi2⟩
      · exact ⟨n,Nat.lt_succ_self n,(lt_of_not_ge hh).le,ht⟩

lemma endpoint_error_bound (f u : ℝ≥0 → ℝ) (h : ℝ≥0) (α : ℝ) (n : ℕ)
    (hz : f 0 = u 0)
    (herr : ∀ i < n, |f ((i:ℝ≥0)*h+h)-f ((i:ℝ≥0)*h)-
      (u ((i:ℝ≥0)*h+h)-u ((i:ℝ≥0)*h))| ≤ α*(h:ℝ)) :
    ∀ i ≤ n, |f ((i:ℝ≥0)*h)-u ((i:ℝ≥0)*h)| ≤ (i:ℝ)*α*(h:ℝ) := by
  intro i hi
  induction i with
  | zero => simp [hz]
  | succ i ih =>
    have hei : ((i+1:ℕ):ℝ≥0)*h = (i:ℝ≥0)*h+h := by push_cast; ring
    rw [hei]
    have hh := herr i (by omega)
    have hh2 := ih (by omega)
    calc
      _ = |(f ((i:ℝ≥0)*h+h)-f ((i:ℝ≥0)*h)-
            (u ((i:ℝ≥0)*h+h)-u ((i:ℝ≥0)*h)))+
            (f ((i:ℝ≥0)*h)-u ((i:ℝ≥0)*h))| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add hh hh2
      _ = _ := by push_cast; ring

lemma tube_of_steps (f u : ℝ≥0 → ℝ) (hf : Continuous f) (h : ℝ≥0) (n : ℕ)
    (hn : 0 < n) {α b L : ℝ} (hα : 0 ≤ α) (hL : 0 ≤ L) (hz : f 0=u 0)
    (hu : ∀ s ∈ Icc 0 ((n:ℝ≥0)*h), ∀ t ∈ Icc 0 ((n:ℝ≥0)*h),
      |u s-u t| ≤ L*|((s:ℝ)-(t:ℝ))|)
    (hs : ∀ i < n, (fun s => f ((i:ℝ≥0)*h+s)-f ((i:ℝ≥0)*h)) ∈
      stepSet h (u ((i:ℝ≥0)*h+h)-u ((i:ℝ≥0)*h)) α b) :
    ∀ t ∈ Icc 0 ((n:ℝ≥0)*h), |f t-u t| ≤ b+(n:ℝ)*α*(h:ℝ)+L*(h:ℝ) := by
  have he := endpoint_error_bound f u h α n hz (fun i hi => (hs i hi).1.le)
  intro t ht
  obtain ⟨i,hi,hit,hti⟩ := exists_grid_interval h hn ht.2
  have hiadd : ((i+1:ℕ):ℝ≥0)*h = (i:ℝ≥0)*h+h := by push_cast; ring
  have hsub : t-(i:ℝ≥0)*h ≤ h := by
    rw [tsub_le_iff_right]
    rw [hiadd] at hti
    simpa only [add_comm] using hti
  have hosc : |f t-f ((i:ℝ≥0)*h)| ≤ b := by
    have hc : Continuous (fun s => f ((i:ℝ≥0)*h+s)-f ((i:ℝ≥0)*h)) :=
      (hf.comp (continuous_const.add continuous_id)).sub continuous_const
    have hh := probe_bound_all hc h (hs i hi).2 (t-(i:ℝ≥0)*h) hsub
    simpa only [add_tsub_cancel_of_le hit] using hh
  have hig : (i:ℝ≥0)*h ≤ (n:ℝ≥0)*h := by gcongr
  have hul : |u ((i:ℝ≥0)*h)-u t| ≤ L*(h:ℝ) := by
    apply (hu _ ⟨bot_le,hig⟩ _ ht).trans
    have habs : |((i:ℝ≥0)*h:ℝ)-(t:ℝ)| ≤ (h:ℝ) := by
      simp only [NNReal.coe_natCast]
      rw [abs_of_nonpos (sub_nonpos.2 (show (i:ℝ)*(h:ℝ) ≤ (t:ℝ) by exact_mod_cast hit))]
      have htR : (t:ℝ) ≤ (i:ℝ)*(h:ℝ)+(h:ℝ) := by exact_mod_cast (hiadd ▸ hti)
      linarith
    exact mul_le_mul_of_nonneg_left habs hL
  calc
    _ = |(f t-f ((i:ℝ≥0)*h))+(f ((i:ℝ≥0)*h)-u ((i:ℝ≥0)*h))+
          (u ((i:ℝ≥0)*h)-u t)| := by congr 1; ring
    _ ≤ (|f t-f ((i:ℝ≥0)*h)|+|f ((i:ℝ≥0)*h)-u ((i:ℝ≥0)*h)|)+
          |u ((i:ℝ≥0)*h)-u t| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ b+(i:ℝ)*α*(h:ℝ)+L*(h:ℝ) := add_le_add (add_le_add hosc (he i hi.le)) hul
    _ ≤ _ := by gcongr

end SLEExactGauge.BrownianSupport

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BrownianSupport

lemma lipschitzTube_pos {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (T : ℝ≥0) (u : ℝ≥0 → ℝ)
    (hu0 : u 0=0) {L : ℝ} (hL : 0 ≤ L)
    (hu : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, |u s-u t| ≤ L*|(s:ℝ)-(t:ℝ)|)
    {ε : ℝ} (hε : 0 < ε) :
    0 < P {sample | ∀ t ∈ Icc 0 T, |B t sample-u t| < ε} := by
  by_cases hT : T=0
  · have hsub : (univ : Set Ω) ≤ᵐ[P] {sample | ∀ t ∈ Icc 0 T, |B t sample-u t| < ε} := by
      filter_upwards [hB.eval_zero_ae_eq_zero] with sample hs _
      intro t ht
      have ht0 : t=0 := le_antisymm (ht.2.trans hT.le) bot_le
      simpa [ht0,hs,hu0] using hε
    have hm := measure_mono_ae hsub
    rw [measure_univ] at hm
    exact zero_lt_one.trans_le hm
  have hTp : 0 < T := lt_of_le_of_ne bot_le (Ne.symm hT)
  have hTR : 0 < (T:ℝ) := hTp
  let α : ℝ := ε/(4*((T:ℝ)+1))
  let b : ℝ := ε/4
  have hα : 0 < α := by dsimp [α]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨δ,hδ,hd⟩ := small_step_pos hB hL hα hb
  let H : ℝ := min δ ((ε/4)/(L+1))
  have hH : 0 < H := lt_min hδ (div_pos (by positivity) (by linarith))
  obtain ⟨n,hn⟩ := exists_nat_gt (max 1 ((T:ℝ)/H))
  have hnR : 0 < (n:ℝ) := lt_trans (by norm_num) (lt_of_le_of_lt (le_max_left _ _) hn)
  have hnN : 0 < n := by exact_mod_cast hnR
  have hnNN : 0 < (n:ℝ≥0) := by exact_mod_cast hnN
  let h : ℝ≥0 := T/(n:ℝ≥0)
  have hh : 0 < h := div_pos hTp hnNN
  have hhH : (h:ℝ) ≤ H := by
    change (T:ℝ)/(n:ℝ) ≤ H
    apply (div_le_iff₀ hnR).2
    have hx := (div_lt_iff₀ hH).1 (lt_of_le_of_lt (le_max_right _ _) hn)
    linarith
  have hhδ : (h:ℝ) ≤ δ := hhH.trans (min_le_left _ _)
  have hLtune : L*(h:ℝ) ≤ ε/4 := by
    have h1 := (le_div_iff₀ (by linarith : 0 < L+1)).1 (hhH.trans (min_le_right _ _))
    nlinarith [h.coe_nonneg]
  have hαtune : α*(T:ℝ) ≤ ε/4 := by
    have heq : α*((T:ℝ)+1) = ε/4 := by dsimp [α]; field_simp
    nlinarith
  have hend : (n:ℝ≥0)*h = T := by dsimp [h]; field_simp
  have hendR : (n:ℝ)*(h:ℝ) = T := by exact_mod_cast hend
  let c (i : ℕ) : ℝ := u ((i:ℝ≥0)*h+h)-u ((i:ℝ≥0)*h)
  have hgrid (i : ℕ) (hi : i<n) : (i:ℝ≥0)*h+h ≤ T := by
    calc
      _ = ((i+1:ℕ):ℝ≥0)*h := by push_cast; ring
      _ ≤ (n:ℝ≥0)*h := by gcongr; omega
      _ = _ := hend
  have hc (i : ℕ) (hi : i<n) : |c i| ≤ L*(h:ℝ) := by
    have hs := hu _ ⟨bot_le,hgrid i hi⟩ _ ⟨bot_le,(le_add_right le_rfl).trans (hgrid i hi)⟩
    simpa [c,NNReal.coe_add,abs_of_nonneg h.coe_nonneg] using hs
  have hp : 0 < P (stepsEvent B h c α b n) :=
    stepsEvent_pos hB h c α b n (fun i hi => hd h hh hhδ (c i) (hc i hi) _)
  have hsub : stepsEvent B h c α b n ≤ᵐ[P]
      {sample | ∀ t ∈ Icc 0 T, |B t sample-u t| < ε} := by
    filter_upwards [hB.cont,hB.eval_zero_ae_eq_zero] with sample hcont hzero hs
    have hhbound := tube_of_steps (fun t => B t sample) u hcont h n hnN hα.le hL
      (hzero.trans hu0.symm) (by simpa only [hend] using hu) hs
    intro t ht
    have hbt := hhbound t (by simpa only [hend] using ht)
    have hcst : b+(n:ℝ)*α*(h:ℝ)+L*(h:ℝ) < ε := by
      have heq : (n:ℝ)*α*(h:ℝ) = α*(T:ℝ) := by rw [← hendR]; ring
      rw [heq]
      dsimp [b]
      linarith
    exact hbt.trans_lt hcst
  exact hp.trans_le (measure_mono_ae hsub)

theorem uniformTube_pos {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (T : ℝ≥0) (u : ℝ≥0 → ℝ)
    (hu : ContinuousOn u (Icc 0 T)) (hu0 : u 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    0 < P {sample | ∀ t ∈ Icc 0 T, |B t sample-u t| < ε} := by
  let v : ℝ → ℝ := fun x => u x.toNNReal
  have hv : ContinuousOn v (Icc 0 (T:ℝ)) :=
    hu.comp continuous_real_toNNReal.continuousOn
      (fun x hx => ⟨bot_le,Real.toNNReal_le_iff_le_coe.2 hx.2⟩)
  obtain ⟨p,hp⟩ := exists_polynomial_near_of_continuousOn 0 (T:ℝ) v hv (ε/8) (by positivity)
  let w : ℝ≥0 → ℝ := fun t => p.eval (t:ℝ)-p.eval 0
  have hw0 : w 0=0 := by simp [w]
  have hp0 : |p.eval 0| < ε/8 := by
    have hh := hp 0 ⟨le_rfl,T.coe_nonneg⟩
    simpa [v,hu0] using hh
  have hwu (t : ℝ≥0) (ht : t ∈ Icc 0 T) : |w t-u t| < ε/4 := by
    have hpt : |p.eval (t:ℝ)-u t| < ε/8 := by
      simpa [v] using hp (t:ℝ) ⟨t.coe_nonneg,ht.2⟩
    calc
      _ = |(p.eval (t:ℝ)-u t)-p.eval 0| := by dsimp [w]; congr 1; ring
      _ ≤ |p.eval (t:ℝ)-u t|+|p.eval 0| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (p.eval (t:ℝ)-u t) (-p.eval 0)
      _ < ε/4 := by linarith
  have hpc : ContDiff ℝ 1 (fun x : ℝ => p.eval x) := by
    simpa using p.contDiff_aeval (𝕜:=ℝ) 1
  obtain ⟨L,hL⟩ := hpc.contDiffOn.exists_lipschitzOnWith (by norm_num) (convex_Icc 0 (T:ℝ)) isCompact_Icc
  have hw : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, |w s-w t| ≤ (L:ℝ)*|(s:ℝ)-(t:ℝ)| := by
    intro s hs t ht
    have hh := hL.dist_le_mul (s:ℝ) ⟨s.coe_nonneg,hs.2⟩ (t:ℝ) ⟨t.coe_nonneg,ht.2⟩
    simpa [w,Real.dist_eq] using hh
  have hpw := lipschitzTube_pos hB T w hw0 L.coe_nonneg hw (show 0 < ε/2 by positivity)
  apply hpw.trans_le
  apply measure_mono
  intro sample hs t ht
  calc
    _ = |(B t sample-w t)+(w t-u t)| := by congr 1; ring
    _ ≤ |B t sample-w t|+|w t-u t| := abs_add_le _ _
    _ < ε := by linarith [hs t ht,hwu t ht]

end SLEExactGauge.BrownianSupport

end

end

end OAI
