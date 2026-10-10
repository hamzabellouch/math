import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.FlowDerivatives

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
namespace ExactSLEGenerator
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
theorem compact_smooth_brownian_martingale
    (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (X : ℝ≥0 → Driver → E) (hXc : ∀ b, Continuous (fun t => X t b))
    (hXm : ∀ t, Measurable[rawFiltration t] (X t))
    (A : E → E) (hAc : Continuous A) (K : ℝ) (hK : 0 ≤ K) (hAb : ∀ x, ‖A x‖ ≤ K)
    (e : E) (he : ‖e‖ ≤ 1)
    (hXeq : ∀ (s h : ℝ≥0) b, X (s+h) b = X s b + increment s h b • e +
      ∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X t.toNNReal b))
    (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f) :
    Martingale (fun t b => f (X t b) - ∫ u in (0 : ℝ)..(t : ℝ),
      ((1/2 : ℝ) * directional 2 f e (X u.toNNReal b) +
        fderiv ℝ f (X u.toNNReal b) (A (X u.toNNReal b)))) rawFiltration W := by
  obtain ⟨C,M,hC,hM,hLip,hThird,hfb,hDb,hQb⟩ := compact_smooth_test_bounds f hf hfc e
  have hQc : Continuous (fun x => iteratedDeriv 2 (fun r : ℝ => f (x+r • e)) 0) := by
    simp_rw [iteratedDeriv_line f hf e,zero_smul,add_zero]
    exact (directional_contDiff f hf e 2).continuous
  have hf3 : ContDiff ℝ 3 f := hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hSmooth (x : E) : ContDiff ℝ 3 (fun w : ℝ => f (x+w • e)) :=
    hf3.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have h := additive_brownian_martingale W hW X hXc hXm A hAc K hK hAb e he hXeq f
    (fderiv ℝ f) (fun x => (hf.differentiable (by simp) x).hasFDerivAt)
    (hf.continuous_fderiv (by simp)) C M hC hM hLip hSmooth hThird hQc hfb hDb hQb
  simpa only [iteratedDeriv_line f hf e,zero_smul,add_zero] using h

end ExactSLEGenerator

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace ExactSLEOptional
variable {Ω : Type*} {m : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 m)
noncomputable def roundUp (N : ℕ) (s : ℝ≥0) : ℝ≥0 := (⌈(N : ℝ≥0) * s⌉₊ : ℝ≥0) / N

theorem le_roundUp {N : ℕ} (hN : 0 < N) (s : ℝ≥0) : s ≤ roundUp N s := by
  rw [roundUp, le_div_iff₀ (by exact_mod_cast hN)]
  simpa [mul_comm] using Nat.le_ceil ((N : ℝ≥0) * s)

theorem roundUp_lt {N : ℕ} (hN : 0 < N) (s : ℝ≥0) :
    roundUp N s < s + (N : ℝ≥0)⁻¹ := by
  rw [roundUp, div_lt_iff₀ (by exact_mod_cast hN)]
  have h := Nat.ceil_lt_add_one (a := (N : ℝ≥0) * s) bot_le
  have hn : (N : ℝ≥0) ≠ 0 := by exact_mod_cast hN.ne'
  simpa [add_mul, mul_add, hn, mul_comm] using h

theorem roundUp_le_iff {N : ℕ} (hN : 0 < N) (s t : ℝ≥0) :
    roundUp N s ≤ t ↔ s ≤ (⌊(N : ℝ≥0) * t⌋₊ : ℝ≥0) / N := by
  have hn : (0 : ℝ≥0) < N := by exact_mod_cast hN
  rw [roundUp, div_le_iff₀ hn, le_div_iff₀ hn, mul_comm t, mul_comm s]
  rw [← Nat.le_floor_iff bot_le, Nat.ceil_le]

theorem roundUp_stopping (S : Ω → ℝ≥0)
    (hS : IsStoppingTime ℱ (fun b => (S b : WithTop ℝ≥0)))
    {N : ℕ} (hN : 0 < N) :
    IsStoppingTime ℱ (fun b => (roundUp N (S b) : WithTop ℝ≥0)) := by
  intro t
  have ht : (⌊(N : ℝ≥0) * t⌋₊ : ℝ≥0) / N ≤ t := by
    rw [div_le_iff₀ (by exact_mod_cast hN), mul_comm t]
    exact Nat.floor_le bot_le
  have he : {b : Ω | (roundUp N (S b) : WithTop ℝ≥0) ≤ t} =
      {b : Ω | (S b : WithTop ℝ≥0) ≤ (((⌊(N : ℝ≥0) * t⌋₊ : ℝ≥0) / N : ℝ≥0) : WithTop ℝ≥0)} := by
    ext b
    exact_mod_cast roundUp_le_iff hN (S b) t
  rw [he]
  exact ℱ.mono ht _ (hS _)

lemma roundUp_tendsto (s : ℝ≥0) :
    Tendsto (fun n : ℕ => roundUp (n + 1) s) atTop (𝓝 s) := by
  have hi : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hr : Tendsto (fun n : ℕ => s + ((n + 1 : ℕ) : ℝ≥0)⁻¹) atTop (𝓝 s) := by
    simpa using tendsto_const_nhds.add hi
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr
    (fun n => le_roundUp (Nat.succ_pos n) s) (fun n => (roundUp_lt (Nat.succ_pos n) s).le)

lemma roundUp_le_add_one {N : ℕ} (hN : 0 < N) (s : ℝ≥0) :
    roundUp N s ≤ s+1 := by
  exact (roundUp_lt hN s).le.trans (add_le_add le_rfl
    ((inv_le_one₀ (by exact_mod_cast hN : (0 : ℝ≥0) < (N : ℝ≥0))).mpr
      (by exact_mod_cast Nat.succ_le_iff.mpr hN)))

lemma roundUp_countable_range (S : Ω → ℝ≥0) (N : ℕ) :
    (Set.range (fun ω => (roundUp N (S ω) : WithTop ℝ≥0))).Countable := by
  apply (Set.countable_range (fun k : ℕ => (((k : ℝ≥0)/N : ℝ≥0) : WithTop ℝ≥0))).mono
  rintro _ ⟨ω,rfl⟩
  exact ⟨⌈(N : ℝ≥0) * S ω⌉₊,rfl⟩

variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {M : ℝ≥0 → Ω → ℝ}

omit [IsFiniteMeasure μ] in
lemma stopped_measurable (hM : Martingale M ℱ μ) (hc : ∀ ω, Continuous (fun t => M t ω))
    (S : Ω → ℝ≥0) (hS : IsStoppingTime ℱ (fun ω => (S ω : WithTop ℝ≥0))) :
    Measurable (fun ω => M (S ω) ω) := by
  exact
    (measurable_stoppedValue (hM.stronglyAdapted.isStronglyProgressive_of_continuous hc) hS).mono hS.measurableSpace_le le_rfl

 

lemma setIntegral_stopped_eq_terminal (hM : Martingale M ℱ μ)
    (hc : ∀ ω, Continuous (fun t => M t ω)) (K : ℝ≥0) (C : ℝ)
    (hb : ∀ t ≤ K+1, ∀ ω, ‖M t ω‖ ≤ C)
    (S : Ω → ℝ≥0) (hS : IsStoppingTime ℱ (fun ω => (S ω : WithTop ℝ≥0)))
    (hSK : ∀ ω, S ω ≤ K) (A : Set Ω) (hA : MeasurableSet[hS.measurableSpace] A) :
    ∫ ω in A, M (S ω) ω ∂μ = ∫ ω in A, M (K+1) ω ∂μ := by
  have heq (n : ℕ) : ∫ ω in A, M (roundUp (n+1) (S ω)) ω ∂μ =
      ∫ ω in A, M (K+1) ω ∂μ := by
    let Sn := fun ω => (roundUp (n+1) (S ω) : WithTop ℝ≥0)
    have hSn : IsStoppingTime ℱ Sn := roundUp_stopping ℱ S hS (Nat.succ_pos n)
    have hbnd : ∀ ω, Sn ω ≤ (K+1 : ℝ≥0) := by
      intro ω
      exact WithTop.coe_le_coe.mpr ((roundUp_le_add_one (Nat.succ_pos n) (S ω)).trans (add_le_add (hSK ω) le_rfl))
    have hm := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range
      hSn hbnd (roundUp_countable_range S (n+1))
    have hASn : MeasurableSet[hSn.measurableSpace] A :=
      hS.measurableSpace_mono hSn (fun ω => WithTop.coe_le_coe.mpr (le_roundUp (Nat.succ_pos n) (S ω))) _ hA
    calc
      _ = ∫ ω in A, stoppedValue M Sn ω ∂μ := by
        congr 1
      _ = ∫ ω in A, μ[M (K+1) | hSn.measurableSpace] ω ∂μ :=
        integral_congr_ae (ae_restrict_of_ae hm)
      _ = _ := setIntegral_condExp hSn.measurableSpace_le (hM.integrable _) hASn
  have ht : Tendsto (fun n : ℕ => ∫ ω in A, M (roundUp (n+1) (S ω)) ω ∂μ)
      atTop (𝓝 (∫ ω in A, M (S ω) ω ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · intro n
      exact (stopped_measurable ℱ hM hc _ (roundUp_stopping ℱ S hS (Nat.succ_pos n))).aestronglyMeasurable
    · exact integrable_const C
    · intro n
      exact Filter.Eventually.of_forall fun ω => hb _
        ((roundUp_le_add_one (Nat.succ_pos n) (S ω)).trans (add_le_add (hSK ω) le_rfl)) ω
    · exact Filter.Eventually.of_forall fun ω => (hc ω).tendsto (S ω) |>.comp (roundUp_tendsto (S ω))
  exact tendsto_nhds_unique ht (by simp_rw [heq]; exact tendsto_const_nhds)

lemma setIntegral_optional_sampling (hM : Martingale M ℱ μ)
    (hc : ∀ ω, Continuous (fun t => M t ω)) (K : ℝ≥0) (C : ℝ)
    (hb : ∀ t ≤ K+1, ∀ ω, ‖M t ω‖ ≤ C)
    (S T : Ω → ℝ≥0)
    (hS : IsStoppingTime ℱ (fun ω => (S ω : WithTop ℝ≥0)))
    (hT : IsStoppingTime ℱ (fun ω => (T ω : WithTop ℝ≥0)))
    (hST : ∀ ω, S ω ≤ T ω) (hTK : ∀ ω, T ω ≤ K)
    (A : Set Ω) (hA : MeasurableSet[hS.measurableSpace] A) :
    ∫ ω in A, M (S ω) ω ∂μ = ∫ ω in A, M (T ω) ω ∂μ := by
  rw [setIntegral_stopped_eq_terminal ℱ hM hc K C hb S hS (fun ω => (hST ω).trans (hTK ω)) A hA,
    setIntegral_stopped_eq_terminal ℱ hM hc K C hb T hT hTK A
      (hS.measurableSpace_mono hT (fun ω => WithTop.coe_le_coe.mpr (hST ω)) _ hA)]

end ExactSLEOptional

namespace ExactSLEGenerator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

noncomputable def generator (f : E → ℝ) (A : E → E) (e : E) (x : E) : ℝ :=
  (1/2 : ℝ) * directional 2 f e x + fderiv ℝ f x (A x)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma generator_continuous (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (A : E → E) (hA : Continuous A) (e : E) : Continuous (generator f A e) :=
  (continuous_const.mul (directional_contDiff f hf e 2).continuous).add
    ((hf.continuous_fderiv (by simp)).clm_apply hA)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma compact_generator_bounds (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hfc : HasCompactSupport f) (A : E → E) (K : ℝ) (hK : 0 ≤ K)
    (hAb : ∀ x, ‖A x‖ ≤ K) (e : E) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧ (∀ x, ‖f x‖ ≤ M) ∧
      (∀ x, ‖generator f A e x‖ ≤ C) := by
  obtain ⟨D,M,hD,hM,hLip,hThird,hfb,hDb,hQb⟩ := compact_smooth_test_bounds f hf hfc e
  refine ⟨M,M/2+M*K,hM,by positivity,?_,?_⟩
  · intro x
    exact hfb x
  · intro x
    have hq : ‖directional 2 f e x‖ ≤ M := by
      simpa only [iteratedDeriv_line f hf e,zero_smul,add_zero,Real.norm_eq_abs] using hQb x
    have hv : ‖fderiv ℝ f x (A x)‖ ≤ M*K :=
      ((fderiv ℝ f x).le_opNorm _).trans (mul_le_mul (hDb x) (hAb x) (norm_nonneg _) hM)
    calc
      _ ≤ ‖(1/2 : ℝ)*directional 2 f e x‖ + ‖fderiv ℝ f x (A x)‖ := norm_add_le _ _
      _ ≤ (1/2 : ℝ)*M+M*K := add_le_add (by
        rw [norm_mul,Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
        exact mul_le_mul_of_nonneg_left hq (by norm_num)) hv
      _ = _ := by ring

 

theorem compact_test_optional_sampling
    (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (X : ℝ≥0 → Driver → E) (hXc : ∀ b, Continuous (fun t => X t b))
    (hXm : ∀ t, Measurable[rawFiltration t] (X t))
    (A : E → E) (hAc : Continuous A) (K : ℝ) (hK : 0 ≤ K) (hAb : ∀ x, ‖A x‖ ≤ K)
    (e : E) (he : ‖e‖ ≤ 1)
    (hXeq : ∀ (s h : ℝ≥0) b, X (s+h) b = X s b + increment s h b • e +
      ∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X t.toNNReal b))
    (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (S T : Driver → ℝ≥0) (B : ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hST : ∀ b, S b ≤ T b) (hTB : ∀ b, T b ≤ B)
    (hzero : ∀ b t, t ≤ T b → generator f A e (X t b) = 0)
    (U : Set Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    ∫ b in U, f (X (S b) b) ∂W = ∫ b in U, f (X (T b) b) ∂W := by
  let M : ℝ≥0 → Driver → ℝ := fun t b => f (X t b) -
    ∫ u in (0 : ℝ)..(t : ℝ), generator f A e (X u.toNNReal b)
  have hM : Martingale M rawFiltration W :=
    compact_smooth_brownian_martingale W hW X hXc hXm A hAc K hK hAb e he hXeq f hf hfc
  have hc (b : Driver) : Continuous (fun t => M t b) := by
    have hg : Continuous (fun u : ℝ => generator f A e (X u.toNNReal b)) :=
      (generator_continuous f hf A hAc e).comp ((hXc b).comp continuous_real_toNNReal)
    exact (hf.continuous.comp (hXc b)).sub
      ((intervalIntegral.continuous_primitive (fun s t => hg.intervalIntegrable s t) 0).comp NNReal.continuous_coe)
  obtain ⟨C,D,hC,hD,hfb,hgb⟩ := compact_generator_bounds f hf hfc A K hK hAb e
  have hb (t : ℝ≥0) (ht : t ≤ B+1) (b : Driver) : ‖M t b‖ ≤ C+D*(B+1) := by
    calc
      _ ≤ ‖f (X t b)‖ + ‖∫ u in (0 : ℝ)..(t : ℝ), generator f A e (X u.toNNReal b)‖ := norm_sub_le _ _
      _ ≤ C+D*(t : ℝ) := add_le_add (hfb _) (by
        simpa only [sub_zero,abs_of_nonneg t.coe_nonneg] using
          intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (t : ℝ))
            (fun u _ => hgb (X u.toNNReal b)))
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (by exact_mod_cast ht) hD)
  have heq (b : Driver) (t : ℝ≥0) (ht : t ≤ T b) : M t b = f (X t b) := by
    change f (X t b) - _ = _
    suffices (∫ u in (0 : ℝ)..(t : ℝ), generator f A e (X u.toNNReal b)) = 0 by rw [this,sub_zero]
    apply Eq.trans _ (intervalIntegral.integral_zero (a := (0 : ℝ)) (b := (t : ℝ)) (μ := volume) (E := ℝ))
    apply intervalIntegral.integral_congr
    intro u hu
    apply hzero b u.toNNReal
    have hu' : u ≤ (t : ℝ) := (by simpa only [uIcc_of_le t.coe_nonneg] using hu : u ∈ Icc 0 (t : ℝ)).2
    exact (Real.toNNReal_le_toNNReal hu').trans (by simpa using ht)
  have ho := ExactSLEOptional.setIntegral_optional_sampling rawFiltration hM hc B
    (C+D*(B+1)) hb S T hS hT hST hTB U hU
  simpa only [heq _ _ (hST _),heq _ _ le_rfl] using ho

end ExactSLEGenerator

namespace ExactSLEMain

abbrev Driver := {b : C(ℝ≥0, ℝ) // b 0 = 0}
instance : MeasurableSpace Driver := borel Driver

def odeUntil (A : ℝ) (b : ℝ≥0 → ℝ) (z : ℂ) (t : ℝ≥0) (f : ℝ → ℂ) : Prop :=
  f 0 = z ∧ ∀ u ∈ Set.Icc 0 (t : ℝ),
    0 < (f u).im ∧ HasDerivWithinAt f ((A : ℂ) / (f u - (b u.toNNReal : ℂ)))
      (Set.Icc 0 (t : ℝ)) u

def alive (A : ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) (z : ℂ) : Prop :=
  ∃ f : ℝ → ℂ, odeUntil A b z t f

noncomputable def loewnerMap (A : ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) (z : ℂ) : ℂ := by
  classical
  exact if h : alive A b t z then (Classical.choose h) t else 0

theorem odeUntil_continuousOn {A : ℝ} {b : ℝ≥0 → ℝ} {z : ℂ} {t : ℝ≥0}
    {f : ℝ → ℂ} (hf : odeUntil A b z t f) : ContinuousOn f (Set.Icc 0 (t : ℝ)) := by
  exact HasDerivWithinAt.continuousOn (fun u hu => (hf.2 u hu).2)

theorem odeUntil_height_lower {A : ℝ} {b : ℝ≥0 → ℝ} {z : ℂ} {t : ℝ≥0}
    {f : ℝ → ℂ} (hf : odeUntil A b z t f) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ Set.Icc 0 (t : ℝ), ε ≤ (f u).im := by
  have hnon : (Set.Icc 0 (t : ℝ)).Nonempty := ⟨0, by simp⟩
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn hnon
    (Complex.continuous_im.comp_continuousOn (odeUntil_continuousOn hf))
  exact ⟨(f u).im, (hf.2 u hu).1, hmin⟩

theorem loewner_vector_difference (A β ε : ℝ) (hε : 0 < ε) (v w : ℂ)
    (hv : ε ≤ v.im) (hw : ε ≤ w.im) :
    ‖(A : ℂ) / (v - (β : ℂ)) - (A : ℂ) / (w - (β : ℂ))‖ ≤
      (|A| / ε ^ 2) * ‖v - w‖ := by
  have hv0 : 0 < v.im := hε.trans_le hv
  have hw0 : 0 < w.im := hε.trans_le hw
  have hnv : ε ≤ ‖v - (β : ℂ)‖ := by
    calc
      ε ≤ v.im := hv
      _ = (v - (β : ℂ)).im := by simp
      _ ≤ _ := Complex.im_le_norm _
  have hnw : ε ≤ ‖w - (β : ℂ)‖ := by
    calc
      ε ≤ w.im := hw
      _ = (w - (β : ℂ)).im := by simp
      _ ≤ _ := Complex.im_le_norm _
  have hvz : v - (β : ℂ) ≠ 0 := norm_pos_iff.mp (hε.trans_le hnv)
  have hwz : w - (β : ℂ) ≠ 0 := norm_pos_iff.mp (hε.trans_le hnw)
  have heq : (A : ℂ) / (v - (β : ℂ)) - (A : ℂ) / (w - (β : ℂ)) =
      (-(A : ℂ)) * (v - w) / ((v - (β : ℂ)) * (w - (β : ℂ))) := by
    field_simp
    ring
  rw [heq, norm_div, norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  calc
    |A| * ‖v - w‖ / (‖v - (β : ℂ)‖ * ‖w - (β : ℂ)‖) ≤ |A| * ‖v - w‖ / ε ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hε)
      simpa [pow_two] using mul_le_mul hnv hnw hε.le (norm_nonneg _)
    _ = _ := by ring

theorem odeUntil_unique (A : ℝ) (b : ℝ≥0 → ℝ) (z : ℂ) (t : ℝ≥0)
    {f g : ℝ → ℂ} (hf : odeUntil A b z t f) (hg : odeUntil A b z t g) :
    Set.EqOn f g (Set.Icc 0 (t : ℝ)) := by
  obtain ⟨εf, hεf, hflower⟩ := odeUntil_height_lower hf
  obtain ⟨εg, hεg, hglower⟩ := odeUntil_height_lower hg
  let ε := min εf εg
  have hε : 0 < ε := lt_min hεf hεg
  have hderiv : ∀ u ∈ Set.Ico 0 (t : ℝ), HasDerivWithinAt (fun u => f u - g u)
      ((A : ℂ) / (f u - (b u.toNNReal : ℂ)) - (A : ℂ) / (g u - (b u.toNNReal : ℂ)))
      (Set.Ici u) u := by
    intro u hu
    exact ((hf.2 u (Set.mem_Icc_of_Ico hu)).2.sub (hg.2 u (Set.mem_Icc_of_Ico hu)).2).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hu)
  have hzero : ∀ u ∈ Set.Icc 0 (t : ℝ), f u - g u = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      ((odeUntil_continuousOn hf).sub (odeUntil_continuousOn hg)) hderiv
      (show f 0 - g 0 = 0 by rw [hf.1, hg.1, sub_self])
    intro u hu
    exact loewner_vector_difference A (b u.toNNReal) ε hε (f u) (g u)
      ((min_le_left _ _).trans (hflower u (Set.mem_Icc_of_Ico hu)))
      ((min_le_right _ _).trans (hglower u (Set.mem_Icc_of_Ico hu)))
  exact fun u hu => sub_eq_zero.mp (hzero u hu)

theorem odeUntil_mono {A : ℝ} {b : ℝ≥0 → ℝ} {z : ℂ} {s t : ℝ≥0}
    {f : ℝ → ℂ} (hf : odeUntil A b z t f) (hst : s ≤ t) : odeUntil A b z s f := by
  refine ⟨hf.1, fun u hu => ?_⟩
  have hsub : Set.Icc 0 (s : ℝ) ⊆ Set.Icc 0 (t : ℝ) :=
    Set.Icc_subset_Icc_right (show (s : ℝ) ≤ t from hst)
  exact ⟨(hf.2 u (hsub hu)).1, (hf.2 u (hsub hu)).2.mono hsub⟩

theorem alive_mono {A : ℝ} {b : ℝ≥0 → ℝ} {z : ℂ} {s t : ℝ≥0}
    (h : alive A b t z) (hst : s ≤ t) : alive A b s z := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, odeUntil_mono hf hst⟩

theorem loewnerMap_eq {A : ℝ} {b : ℝ≥0 → ℝ} {z : ℂ} {t : ℝ≥0}
    {f : ℝ → ℂ} (hf : odeUntil A b z t f) : loewnerMap A b t z = f t := by
  have he : alive A b t z := ⟨f, hf⟩
  rw [loewnerMap, dite_eq_left he]
  exact odeUntil_unique A b z t (Classical.choose_spec he) hf (by simp)

def shiftDriver (b : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ≥0 → ℝ := fun u => b (s + u) - b s

theorem odeUntil_shift {A : ℝ} {b : ℝ≥0 → ℝ} {z : ℂ} {s t : ℝ≥0}
    {f : ℝ → ℂ} (hf : odeUntil A b z (s + t) f) :
    odeUntil A (shiftDriver b s) (f s - (b s : ℂ)) t
      (fun u => f (u + s) - (b s : ℂ)) := by
  refine ⟨by simp, fun u hu => ?_⟩
  have hmaps : Set.MapsTo (fun u : ℝ => u + s) (Set.Icc 0 (t : ℝ)) (Set.Icc 0 ((s + t : ℝ≥0) : ℝ)) := by
    intro v hv
    constructor <;> simp only [NNReal.coe_add] <;> linarith [s.coe_nonneg, hv.1, hv.2]
  have hnn : (u + (s : ℝ)).toNNReal = s + u.toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal _ (add_nonneg hu.1 s.coe_nonneg),
      Real.coe_toNNReal _ hu.1]
    ring
  have hder := ((hf.2 (u + s) (hmaps hu)).2.scomp u
    ((hasDerivAt_id u).add_const (s : ℝ)).hasDerivWithinAt hmaps).sub_const (b s : ℂ)
  constructor
  · simpa using (hf.2 (u + s) (hmaps hu)).1
  · simpa [shiftDriver, hnn, sub_sub_sub_cancel_right] using hder

theorem loewnerMap_restart (A : ℝ) (b : ℝ≥0 → ℝ) (z : ℂ) (s t : ℝ≥0)
    (h : alive A b (s + t) z) :
    alive A (shiftDriver b s) t (loewnerMap A b s z - (b s : ℂ)) ∧
    loewnerMap A (shiftDriver b s) t (loewnerMap A b s z - (b s : ℂ)) =
      loewnerMap A b (s + t) z - (b s : ℂ) := by
  obtain ⟨f, hf⟩ := h
  have hs : odeUntil A b z s f := odeUntil_mono hf (by exact le_add_of_nonneg_right (show 0 ≤ t from bot_le))
  have hfs := loewnerMap_eq hs
  rw [hfs]
  constructor
  · exact ⟨_, odeUntil_shift hf⟩
  · rw [loewnerMap_eq (odeUntil_shift hf), loewnerMap_eq hf]
    simp [add_comm]

end ExactSLEMain
end

end OAI
