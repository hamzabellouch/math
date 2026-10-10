import Mathlib
import OAI.Probability.SKValue.Equations.GradientStrip
import OAI.Probability.SKValue.Equations.InitialMax

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue

lemma brownian_increment_indep_past
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F) :
    IndepFun (fun ω ↦ B t ω-B s ω) F μ := by
  have h := (hB.indepFun_shift s).comp (measurable_pi_apply (t-s)) measurable_id
  simp only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst] at h
  change Indep (MeasurableSpace.comap (fun ω ↦ B t ω-B s ω) inferInstance)
    (MeasurableSpace.comap (fun ω (r : Iic s) ↦ B r ω) inferInstance) μ at h
  change Indep (MeasurableSpace.comap (fun ω ↦ B t ω-B s ω) inferInstance)
    (MeasurableSpace.comap F inferInstance) μ
  apply indep_of_indep_of_le_right h
  rw [←Filtration.natural_eq_comap B hBm s]
  exact hF.measurable.comap_le

lemma brownian_increment_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (s t : ℝ≥0) :
    (∫ ω, B t ω-B s ω ∂μ)=0 := by
  change (∫ ω, (B t-B s) ω ∂μ)=0
  rw [(hB.hasLaw_sub t s).integral_eq, integral_id_gaussianReal]

lemma brownian_increment_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {s t : ℝ≥0} (hst : s≤t) :
    (∫ ω, (B t ω-B s ω)^2 ∂μ)=(t : ℝ)-s := by
  have hv := (hB.hasLaw_sub t s).variance_eq
  rw [variance_id_gaussianReal] at hv
  rw [variance_eq_integral (hB.hasLaw_sub t s).aemeasurable] at hv
  simp only [Pi.sub_apply, brownian_increment_integral hB s t, sub_zero] at hv
  have ht' : (s : ℝ)≤t := by exact_mod_cast hst
  exact hv.trans (show (nndist (t:ℝ) (s:ℝ) : ℝ)=(t:ℝ)-s from by
    change |(t:ℝ)-(s:ℝ)|=(t:ℝ)-s
    exact abs_of_nonneg (sub_nonneg.mpr ht'))

lemma brownian_predictable_increment_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F)
    (hFi : Integrable F μ) : Integrable (fun ω ↦ F ω*(B t ω-B s ω)) μ := by
  exact (brownian_increment_indep_past hB hBm hst hF).symm.integrable_mul hFi
    ((hB.hasLaw_sub t s).hasGaussianLaw.memLp_two.integrable (by norm_num))

lemma brownian_predictable_increment_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F) :
    (∫ ω, F ω*(B t ω-B s ω) ∂μ)=0 := by
  have hFm := hF.mono (Filtration.le _ s)
  have h := (brownian_increment_indep_past hB hBm hst hF).symm.integral_mul_eq_mul_integral
    hFm.aestronglyMeasurable ((hBm t).sub (hBm s)).aestronglyMeasurable
  simpa only [Pi.mul_apply, brownian_increment_integral hB s t, mul_zero] using h

lemma brownian_predictable_quadratic_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F)
    (hFi : Integrable F μ) :
    Integrable (fun ω ↦ F ω*((B t ω-B s ω)^2-((t : ℝ)-s))) μ := by
  have h := (brownian_increment_indep_past hB hBm hst hF).comp
    (φ := fun x : ℝ ↦ x^2-((t : ℝ)-s))
    ((measurable_id.pow_const 2).sub measurable_const) measurable_id
  have hi : Integrable (fun ω ↦ (B t ω-B s ω)^2-((t : ℝ)-s)) μ :=
    ((hB.hasLaw_sub t s).hasGaussianLaw.memLp_two.integrable_sq).sub (integrable_const _)
  exact h.symm.integrable_mul hFi hi

lemma brownian_predictable_quadratic_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F) :
    (∫ ω, F ω*((B t ω-B s ω)^2-((t : ℝ)-s)) ∂μ)=0 := by
  have hFm := hF.mono (Filtration.le _ s)
  have hi : Integrable (fun ω ↦ (B t ω-B s ω)^2) μ :=
    (hB.hasLaw_sub t s).hasGaussianLaw.memLp_two.integrable_sq
  have h0 : (∫ ω, (B t ω-B s ω)^2-((t : ℝ)-s) ∂μ)=0 := by
    rw [integral_sub hi (integrable_const _), brownian_increment_second_moment hB hst]
    simp
  have h := (brownian_increment_indep_past hB hBm hst hF).comp
    (φ := fun x : ℝ ↦ x^2-((t : ℝ)-s))
    ((measurable_id.pow_const 2).sub measurable_const) measurable_id
  have hQm : AEStronglyMeasurable (fun ω ↦ (B t ω-B s ω)^2-((t : ℝ)-s)) μ :=
    (((hBm t).sub (hBm s)).pow 2 |>.sub stronglyMeasurable_const).aestronglyMeasurable
  have heq := h.symm.integral_mul_eq_mul_integral hFm.aestronglyMeasurable hQm
  simpa only [Function.comp_def, id_eq, Pi.mul_apply, h0, mul_zero] using heq

end SKValue

namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped Topology NNReal ENNReal BigOperators

noncomputable def driftDefect (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (X W : ℝ → ℝ) : ℝ :=
  ∑ i : Fin N, |X (meshTime T N (i+1))-X (meshTime T N i)-
    (W (meshTime T N (i+1))-W (meshTime T N i))-
    stepSize T N*γ (meshTime T N i)*u (meshTime T N i) (X (meshTime T N i))|

lemma driftDefect_nonneg (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (X W : ℝ → ℝ) : 0≤driftDefect T N γ u X W :=
  Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)

lemma driftDefect_error_bound {T L ε : ℝ} {N : ℕ} {u : ℝ → ℝ → ℝ}
    {γ W X : ℝ → ℝ} (hT : 0≤T) (hN : 0<N) (hL : 0≤L) (hε : 0≤ε)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hu : ∀ t∈Icc (0 : ℝ) T, ∀ x, |u t x|≤1)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤L*(|s-t|+|x-y|))
    (hXosc : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T,
      |s-t|≤ stepSize T N → |X s-X t|≤ε)
    (hint : IntervalIntegrable (fun s ↦ γ s*u s (X s)) volume 0 T)
    (hX : ∀ t∈Icc (0 : ℝ) T, X t=W t+∫ s in (0 : ℝ)..t, γ s*u s (X s)) :
    driftDefect T N γ u X W ≤
      stepSize T N*(γ T-γ 0)+T*γ T*L*(stepSize T N+ε) := by
  have ht0 : (0 : ℝ)∈Icc (0 : ℝ) T := ⟨le_rfl,hT⟩
  have htT : T∈Icc (0 : ℝ) T := ⟨hT,le_rfl⟩
  have hδ : 0≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  have hN0 : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
  have hmesh : (N : ℝ)*stepSize T N=T := by dsimp [stepSize]; field_simp
  have htime (j : ℕ) (hj : j≤N) : meshTime T N j∈Icc (0 : ℝ) T :=
    mesh_mem_strip_ito hδ hmesh hj
  have hsucc (j : ℕ) : meshTime T N (j+1)=meshTime T N j+stepSize T N := by
    dsimp [meshTime]; push_cast; ring
  have hG : 0≤γ T := hγ0.trans (hγ ht0 htT hT)
  have hγpos (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : 0≤γ t :=
    hγ0.trans (hγ ht0 ht ht.1)
  have hlocal (i : Fin N) :
      |X (meshTime T N (i+1))-X (meshTime T N i)-
        (W (meshTime T N (i+1))-W (meshTime T N i))-
        stepSize T N*γ (meshTime T N i)*u (meshTime T N i) (X (meshTime T N i))|≤
      stepSize T N*(γ (meshTime T N (i+1))-γ (meshTime T N i))+
        stepSize T N*γ T*L*(stepSize T N+ε) := by
    let a := meshTime T N i
    let b := meshTime T N (i+1)
    have ha := htime i i.isLt.le
    have hb := htime (i+1) (by omega)
    have hlen : b-a=stepSize T N := by dsimp [a,b]; rw [hsucc]; ring
    have hab : a≤b := by linarith
    have hsub : Icc a b⊆Icc (0 : ℝ) T := Icc_subset_Icc ha.1 hb.2
    have hh := monotone_drift_local_error hab hG hL hε (hγ.mono hsub)
      (hγpos a ha) (hγ ha htT ha.2) (fun s hs ↦ hu s (hsub hs) _)
      (fun s hs ↦ hLip s (hsub hs) a ha _ _)
      (fun s hs ↦ hXosc s (hsub hs) a ha (by
        rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
        linarith [hs.2]))
      (intervalIntegrable_substrip hT hint ha hb)
    have hdiff : X b-X a-(W b-W a)=∫ s in a..b, γ s*u s (X s) := by
      rw [hX b hb,hX a ha]
      have he := intervalIntegral.integral_interval_sub_left
        (intervalIntegrable_substrip hT hint ht0 hb)
        (intervalIntegrable_substrip hT hint ht0 ha)
      linear_combination he
    dsimp only [a,b] at hdiff hlen
    rw [hdiff]
    simpa only [hlen, a,b] using hh
  calc
    _ ≤ ∑ i : Fin N, (stepSize T N*(γ (meshTime T N (i+1))-γ (meshTime T N i))+
        stepSize T N*γ T*L*(stepSize T N+ε)) := Finset.sum_le_sum (fun i _ ↦ hlocal i)
    _ = _ := by
      rw [Finset.sum_add_distrib, ←Finset.mul_sum, sum_steps_sub (fun j ↦ γ (meshTime T N j))]
      simp only [meshTime, Nat.cast_zero, zero_mul, hmesh, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      linear_combination (γ T*L*(stepSize T N+ε))*hmesh

lemma driftDefect_tendsto {T L : ℝ} {u : ℝ → ℝ → ℝ} {γ W X : ℝ → ℝ}
    (hT : 0≤T) (hL : 0≤L)
    (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (hγ0 : 0≤γ 0)
    (hu : ∀ t∈Icc (0 : ℝ) T, ∀ x, |u t x|≤1)
    (hLip : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |u s x-u t y|≤L*(|s-t|+|x-y|))
    (hXcont : ContinuousOn X (Icc (0 : ℝ) T))
    (hint : IntervalIntegrable (fun s ↦ γ s*u s (X s)) volume 0 T)
    (hX : ∀ t∈Icc (0 : ℝ) T, X t=W t+∫ s in (0 : ℝ)..t, γ s*u s (X s)) :
    Tendsto (fun N ↦ driftDefect T N γ u X W) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hG : 0≤γ T := hγ0.trans (hγ ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT)
  let C := T*γ T*L
  have hC : 0≤C := by dsimp [C]; positivity
  let η := ε/(2*(C+1))
  have hη : 0<η := by dsimp [η]; positivity
  have hηeq : η*(2*(C+1))=ε := div_mul_cancel₀ _ (by positivity)
  have hCη : C*η<ε/2 := by nlinarith
  obtain ⟨θ,hθ,hmod⟩ := Metric.uniformContinuousOn_iff_le.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hXcont) η hη
  have hδ : Tendsto (fun N : ℕ ↦ stepSize T N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have htail : Tendsto (fun N : ℕ ↦ stepSize T N*((γ T-γ 0)+C)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using hδ.mul_const ((γ T-γ 0)+C)
  have hev : ∀ᶠ N in atTop, dist (driftDefect T N γ u X W) 0<ε := by
    filter_upwards [hδ.eventually_le_const hθ, htail.eventually_lt_const (half_pos hε),
      eventually_gt_atTop 0] with N hNθ hNerr hN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (driftDefect_nonneg T N γ u X W)]
    have hh := driftDefect_error_bound hT hN hL hη.le hγ hγ0 hu hLip
      (fun s hs t ht hst ↦ by
        have hst' := hmod s hs t ht (by simpa only [Real.dist_eq] using hst.trans hNθ)
        simpa only [Real.dist_eq] using hst') hint hX
    dsimp only [C] at hCη hNerr
    linarith
  exact eventually_atTop.mp hev

end SKValue

end

end OAI
