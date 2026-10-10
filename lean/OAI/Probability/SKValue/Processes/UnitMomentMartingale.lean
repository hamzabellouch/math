import Mathlib

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

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

structure UnitMomentMartingale (ℱ : Filtration ℝ m) (f : ℝ → Ω → ℝ) : Prop where
  measurable : ∀ t ∈ Ico (0 : ℝ) 1, StronglyMeasurable[ℱ t] (f t)
  bounded : ∀ t ∈ Ico (0 : ℝ) 1, ∀ ω, |f t ω| ≤ 1
  condExp : ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1, s ≤ t →
    μ[f t | ℱ s] =ᵐ[μ] f s
  secondMoment : ∀ t ∈ Ico (0 : ℝ) 1, ∫ ω, (f t ω)^2 ∂μ = t

variable {ℱ : Filtration ℝ m} {f : ℝ → Ω → ℝ}

lemma UnitMomentMartingale.integrable (h : UnitMomentMartingale (μ := μ) ℱ f)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : Integrable (f t) μ :=
  Integrable.of_bound ((h.measurable t ht).mono (ℱ.le t)).aestronglyMeasurable 1
    (Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le (h.bounded t ht ω)))

lemma UnitMomentMartingale.integrable_mul (h : UnitMomentMartingale (μ := μ) ℱ f)
    {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) :
    Integrable (fun ω ↦ f s ω * f t ω) μ :=
  Integrable.of_bound (((h.measurable s hs).mono (ℱ.le s)).mul
    ((h.measurable t ht).mono (ℱ.le t))).aestronglyMeasurable 1
    (Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs,abs_mul]
      nlinarith [h.bounded s hs ω,h.bounded t ht ω,abs_nonneg (f s ω),abs_nonneg (f t ω)]))

lemma UnitMomentMartingale.integral_past_mul (h : UnitMomentMartingale (μ := μ) ℱ f)
    {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) (hst : s ≤ t) :
    ∫ ω, f s ω * f t ω ∂μ = s := by
  have hc := condExp_mul_of_stronglyMeasurable_left (h.measurable s hs)
    (h.integrable_mul hs ht) (h.integrable ht)
  have he : μ[(f s) * (f t) | ℱ s] =ᵐ[μ] fun ω ↦ (f s ω)^2 := by
    filter_upwards [hc,h.condExp s hs t ht hst] with ω hω hω'
    simpa only [Pi.mul_apply,hω',pow_two] using hω
  calc
    _ = ∫ ω, μ[(f s) * (f t) | ℱ s] ω ∂μ := (integral_condExp (ℱ.le s)).symm
    _ = ∫ ω, (f s ω)^2 ∂μ := integral_congr_ae he
    _ = s := h.secondMoment s hs

lemma UnitMomentMartingale.sampled_gap_martingale
    (h : UnitMomentMartingale (μ := μ) ℱ f) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (r : ℕ → ℝ) (hr : Monotone r)
    (hrmem : ∀ n, r n ∈ Ico s 1) :
    Martingale (fun n ω ↦ 1-f s ω*f (r n) ω)
      (⟨fun n ↦ ℱ (r n),fun _ _ hij ↦ ℱ.mono (hr hij),fun n ↦ ℱ.le (r n)⟩ :
        Filtration ℕ m) μ := by
  have ht (n : ℕ) : r n ∈ Ico (0 : ℝ) 1 := ⟨hs.1.trans (hrmem n).1,(hrmem n).2⟩
  refine ⟨fun n ↦ stronglyMeasurable_const.sub
    (((h.measurable s hs).mono (ℱ.mono (hrmem n).1)).mul (h.measurable (r n) (ht n))),?_⟩
  intro i j hij
  have hc := condExp_mul_of_stronglyMeasurable_left
    ((h.measurable s hs).mono (ℱ.mono (hrmem i).1))
    (h.integrable_mul hs (ht j)) (h.integrable (ht j))
  have hc1 := condExp_of_stronglyMeasurable (ℱ.le (r i))
    (stronglyMeasurable_const (b := (1 : ℝ))) (integrable_const (μ := μ) 1)
  filter_upwards [condExp_sub (integrable_const (1 : ℝ))
      (h.integrable_mul hs (ht j)) (ℱ (r i)),hc,
      h.condExp (r i) (ht i) (r j) (ht j) (hr hij)] with ω hsub hmul he
  simp only [Pi.sub_apply] at hsub
  change μ[(fun ω ↦ f s ω*f (r j) ω) | ℱ (r i)] ω =
    f s ω*μ[f (r j) | ℱ (r i)] ω at hmul
  rw [hc1,hmul] at hsub
  simpa only [Pi.sub_def,Pi.mul_def,Pi.mul_apply,he] using hsub

omit [IsProbabilityMeasure μ] in
lemma UnitMomentMartingale.sampled_gap_nonneg
    (h : UnitMomentMartingale (μ := μ) ℱ f) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) (ω : Ω) :
    0 ≤ 1-f s ω*f t ω := by
  have hh : f s ω*f t ω ≤ 1 := calc
    _ ≤ |f s ω*f t ω| := le_abs_self _
    _ = |f s ω| * |f t ω| := abs_mul _ _
    _ ≤ 1 := by nlinarith [h.bounded s hs ω,h.bounded t ht ω,
      abs_nonneg (f s ω),abs_nonneg (f t ω)]
  linarith

lemma UnitMomentMartingale.sampled_gap_integral
    (h : UnitMomentMartingale (μ := μ) ℱ f) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1) (hst : s ≤ t) :
    ∫ ω, 1-f s ω*f t ω ∂μ = 1-s := by
  rw [integral_sub (integrable_const 1) (h.integrable_mul hs ht),
    h.integral_past_mul hs ht hst]
  simp

lemma UnitMomentMartingale.finite_gap_maximal
    (h : UnitMomentMartingale (μ := μ) ℱ f) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (S : Finset ℝ)
    (hS : ∀ t ∈ S, t ∈ Ico s 1) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * μ {ω | ∃ t ∈ S, (ε : ℝ) ≤ 1-f s ω*f t ω} ≤
      ENNReal.ofReal (1-s) := by
  classical
  by_cases hne : S.Nonempty
  · have hcard : 0 < S.card := Finset.card_pos.mpr hne
    let e := S.orderEmbOfFin rfl
    let r : ℕ → ℝ := fun n ↦ e ⟨min n (S.card-1),by omega⟩
    have hr : Monotone r := by
      intro i j hij
      exact e.monotone (show min i (S.card-1) ≤ min j (S.card-1) from min_le_min_right _ hij)
    have hrmem (n : ℕ) : r n ∈ Ico s 1 := hS _ (S.orderEmbOfFin_mem rfl _)
    have hm := h.sampled_gap_martingale hs r hr hrmem
    have hn : 0 ≤ (fun n ω ↦ 1-f s ω*f (r n) ω) :=
      fun n ω ↦ h.sampled_gap_nonneg hs ⟨hs.1.trans (hrmem n).1,(hrmem n).2⟩ ω
    have hb := maximal_ineq hm.submartingale hn (ε := ε) (S.card-1)
    have hset : {ω | ∃ t ∈ S, (ε : ℝ) ≤ 1-f s ω*f t ω} ⊆
        {ω | (ε : ℝ) ≤ (Finset.range ((S.card-1)+1)).sup' Finset.nonempty_range_add_one
          (fun k ↦ 1-f s ω*f (r k) ω)} := by
      rintro ω ⟨t,ht,heps⟩
      let i := (S.orderIsoOfFin rfl).symm ⟨t,ht⟩
      have her : r i.val = t := by
        dsimp only [r]
        have hh : (⟨min i.val (S.card-1),by omega⟩ : Fin S.card) = i :=
          Fin.ext (min_eq_left (by omega))
        rw [hh]
        change ((S.orderIsoOfFin rfl) i).val = t
        simp [i]
      refine heps.trans ?_
      rw [← her]
      exact Finset.le_sup' (f := fun k ↦ 1-f s ω*f (r k) ω)
        (Finset.mem_range.mpr (by omega : i.val < (S.card-1)+1))
    calc
      _ ≤ (ε : ℝ≥0∞) * μ {ω | (ε : ℝ) ≤
          (Finset.range ((S.card-1)+1)).sup' Finset.nonempty_range_add_one
            (fun k ↦ 1-f s ω*f (r k) ω)} := by gcongr
      _ ≤ _ := hb
      _ ≤ ENNReal.ofReal (∫ ω, 1-f s ω*f (r (S.card-1)) ω ∂μ) := by
        apply ENNReal.ofReal_le_ofReal
        exact setIntegral_le_integral (integrable_const 1 |>.sub
          (h.integrable_mul hs ⟨hs.1.trans (hrmem _).1,(hrmem _).2⟩))
          (Eventually.of_forall (hn (S.card-1)))
      _ = _ := congrArg ENNReal.ofReal (h.sampled_gap_integral hs
        ⟨hs.1.trans (hrmem _).1,(hrmem _).2⟩ (hrmem _).1)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

lemma UnitMomentMartingale.rational_gap_maximal
    (h : UnitMomentMartingale (μ := μ) ℱ f) {s : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (ε : ℝ≥0) :
    (ε : ℝ≥0∞) * μ {ω | ∃ q : ℚ, (q : ℝ) ∈ Ico s 1 ∧
      (ε : ℝ) ≤ 1-f s ω*f q ω} ≤ ENNReal.ofReal (1-s) := by
  classical
  let E : Finset ℚ → Set Ω := fun S ↦ {ω | ∃ q ∈ S, (q : ℝ) ∈ Ico s 1 ∧
    (ε : ℝ) ≤ 1-f s ω*f q ω}
  have hd : Directed (· ⊆ ·) E := by
    intro S T
    refine ⟨S∪T, ?_, ?_⟩
    · rintro ω ⟨q,hq,hmem,he⟩
      exact ⟨q,Finset.mem_union_left _ hq,hmem,he⟩
    · rintro ω ⟨q,hq,hmem,he⟩
      exact ⟨q,Finset.mem_union_right _ hq,hmem,he⟩
  have heq : {ω | ∃ q : ℚ, (q : ℝ) ∈ Ico s 1 ∧ (ε : ℝ) ≤ 1-f s ω*f q ω} =
      ⋃ S : Finset ℚ, E S := by
    ext ω
    constructor
    · rintro ⟨q,hmem,he⟩
      exact mem_iUnion.mpr ⟨{q},q,Finset.mem_singleton_self _,hmem,he⟩
    · intro hω
      obtain ⟨S,q,hq,hmem,he⟩ := mem_iUnion.mp hω
      exact ⟨q,hmem,he⟩
  rw [heq,hd.measure_iUnion,ENNReal.mul_iSup]
  refine iSup_le fun S ↦ ?_
  let R : Finset ℝ := (S.filter (fun q : ℚ ↦ (q : ℝ) ∈ Ico s 1)).image (fun q : ℚ ↦ (q : ℝ))
  have hR : ∀ t ∈ R, t ∈ Ico s 1 := by
    intro t ht
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
    exact (Finset.mem_filter.mp hq).2
  have hE : E S ⊆ {ω | ∃ t ∈ R, (ε : ℝ) ≤ 1-f s ω*f t ω} := by
    rintro ω ⟨q,hq,hmem,he⟩
    exact ⟨(q : ℝ),Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hmem⟩,rfl⟩,he⟩
  calc
    _ ≤ (ε : ℝ≥0∞) * μ {ω | ∃ t ∈ R, (ε : ℝ) ≤ 1-f s ω*f t ω} := by gcongr
    _ ≤ _ := h.finite_gap_maximal hs R hR ε

noncomputable def terminalTime (n : ℕ) : ℝ := 1-1/(n+1)

lemma terminalTime_mem (n : ℕ) : terminalTime n ∈ Ico (0 : ℝ) 1 := by
  have hn : (1 : ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hp : (0 : ℝ) < n+1 := by positivity
  simp only [terminalTime]
  constructor
  · have hh : (1 : ℝ)/(n+1) ≤ 1 := (div_le_one hp).mpr hn
    linarith
  · have hh : (0 : ℝ) < 1/(n+1) := by positivity
    linarith

lemma terminalTime_monotone : Monotone terminalTime := by
  intro i j hij
  simp only [terminalTime]
  have hh : (1 : ℝ)/(j+1) ≤ 1/(i+1) := one_div_le_one_div_of_le
    (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  linarith

lemma terminalTime_tendsto : Tendsto terminalTime atTop (𝓝[<] (1 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_,Eventually.of_forall (fun n ↦ (terminalTime_mem n).2)⟩
  change Tendsto (fun n : ℕ ↦ (1 : ℝ)-1/((n : ℝ)+1)) atTop (𝓝 (1 : ℝ))
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma UnitMomentMartingale.ae_exists_rational_gap_bound
    (h : UnitMomentMartingale (μ := μ) ℱ f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∃ n, ∀ q : ℚ, (q : ℝ) ∈ Ico (terminalTime n) 1 →
      1-f (terminalTime n) ω*f q ω < ε := by
  let E : ℕ → Set Ω := fun n ↦ {ω | ∃ q : ℚ, (q : ℝ) ∈ Ico (terminalTime n) 1 ∧
    ε ≤ 1-f (terminalTime n) ω*f q ω}
  have hbound (n : ℕ) : ENNReal.ofReal ε * μ (⋂ n, E n) ≤
      ENNReal.ofReal (1-terminalTime n) := calc
    _ ≤ ENNReal.ofReal ε * μ (E n) := by gcongr; exact iInter_subset E n
    _ ≤ _ := by
      have hh := h.rational_gap_maximal (terminalTime_mem n) (NNReal.mk ε hε.le)
      simpa only [E,NNReal.coe_mk,ENNReal.coe_nnreal_eq] using hh
  have hzero : ENNReal.ofReal ε * μ (⋂ n, E n) = 0 := by
    apply le_antisymm _ bot_le
    have hlim : Tendsto (fun n ↦ ENNReal.ofReal (1-terminalTime n)) atTop (𝓝 0) := by
      have hh : Tendsto (fun n ↦ 1-terminalTime n) atTop (𝓝 (0 : ℝ)) := by
        simpa only [sub_self] using ((tendsto_const_nhds (x := (1 : ℝ))).sub
          (tendsto_nhdsWithin_iff.mp terminalTime_tendsto).1)
      simpa only [ENNReal.ofReal_zero,Function.comp_def] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
    exact ge_of_tendsto' hlim hbound
  have hn : μ (⋂ n, E n) = 0 := (mul_eq_zero.mp hzero).resolve_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  have ha : ∀ᵐ ω ∂μ, ω ∉ ⋂ n, E n := by
    rw [ae_iff]
    convert hn using 1
    simp only [not_not,Set.ofPred_mem_eq]
  filter_upwards [ha] with ω hω
  simp only [mem_iInter,E,mem_ofPred_eq,not_forall,not_exists,not_and,not_le] at hω
  exact hω

lemma continuous_gap_bound_of_rat {v : ℝ → ℝ}
    (hv : ContinuousOn v (Ico (0 : ℝ) 1)) {s ε : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1)
    (hq : ∀ q : ℚ, (q : ℝ) ∈ Ico s 1 → 1-v s*v q < ε) :
    ∀ t ∈ Ioo s 1, 1-v s*v t ≤ ε := by
  intro t ht
  by_contra! he
  have hvt : ContinuousAt v t := (hv t ⟨hs.1.trans ht.1.le,ht.2⟩).continuousAt
    (Ico_mem_nhds_iff.mpr ⟨hs.1.trans_lt ht.1,ht.2⟩)
  have hgt : ContinuousAt (fun r ↦ 1-v s*v r) t := continuousAt_const.sub
    (continuousAt_const.mul hvt)
  have hevent : {r | ε < 1-v s*v r} ∈ 𝓝 t := hgt (Ioi_mem_nhds he)
  obtain ⟨q,hq'⟩ := Rat.denseRange_cast.mem_nhds (inter_mem hevent (Ioo_mem_nhds ht.1 ht.2))
  exact (hq q ⟨hq'.2.1.le,hq'.2.2⟩).not_gt hq'.1

lemma UnitMomentMartingale.exists_sequence_terminal
    (h : UnitMomentMartingale (μ := μ) ℱ f) :
    ∃ U : Ω → ℝ, StronglyMeasurable[ℱ 1] U ∧
      (∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧
        Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω))) := by
  let 𝒢 : Filtration ℕ m := ⟨fun n ↦ ℱ (terminalTime n),
    fun _ _ hij ↦ ℱ.mono (terminalTime_monotone hij),fun n ↦ ℱ.le _⟩
  have hm : Martingale (fun n ↦ f (terminalTime n)) 𝒢 μ :=
    ⟨fun n ↦ h.measurable _ (terminalTime_mem n),fun i j hij ↦
      h.condExp _ (terminalTime_mem i) _ (terminalTime_mem j) (terminalTime_monotone hij)⟩
  have hb (n : ℕ) : eLpNorm (f (terminalTime n)) 1 μ ≤ (1 : ℝ≥0) := by
    have hh := eLpNorm_le_of_ae_bound (μ := μ) (p := (1 : ℝ≥0∞))
      (h.integrable (terminalTime_mem n)).aestronglyMeasurable
      (Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le
        (h.bounded _ (terminalTime_mem n) ω)))
    simpa using hh
  let U := 𝒢.limitProcess (fun n ↦ f (terminalTime n)) μ
  have hU : StronglyMeasurable[ℱ 1] U :=
    Filtration.stronglyMeasurable_limitProcess.mono (iSup_le fun n ↦ ℱ.mono (terminalTime_mem n).2.le)
  refine ⟨U,hU,?_⟩
  filter_upwards [hm.submartingale.ae_tendsto_limitProcess hb] with ω hω
  exact ⟨le_of_tendsto' hω.abs (fun n ↦ h.bounded _ (terminalTime_mem n) ω),hω⟩

lemma UnitMomentMartingale.exists_continuous_terminal
    (h : UnitMomentMartingale (μ := μ) ℱ f)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ f t ω) (Ico (0 : ℝ) 1)) :
    ∃ U : Ω → ℝ, StronglyMeasurable[ℱ 1] U ∧
      (∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧
        Tendsto (fun t ↦ f t ω) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) := by
  obtain ⟨U,hU,hseq⟩ := h.exists_sequence_terminal
  have hg : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∃ n, ∀ q : ℚ,
      (q : ℝ) ∈ Ico (terminalTime n) 1 →
        1-f (terminalTime n) ω*f q ω < 1/(k+1) := by
    apply ae_all_iff.mpr
    intro k
    exact h.ae_exists_rational_gap_bound (by positivity)
  refine ⟨U,hU,?_⟩
  filter_upwards [hc,hseq,hg] with ω hcont hseqω hgap
  refine ⟨hseqω.1,Metric.tendsto_nhds.mpr (fun δ hδ ↦ ?_)⟩
  obtain ⟨k,hk⟩ : ∃ k : ℕ, (1 : ℝ)/(k+1) < δ^2/32 := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iio_mem_nhds (show (0 : ℝ) < δ^2/32 by positivity))
    exact hh.exists
  obtain ⟨n,hn⟩ := hgap k
  have hreal := continuous_gap_bound_of_rat hcont (terminalTime_mem n) hn
  have hbound (t : ℝ) (ht : t ∈ Ioo (terminalTime n) 1) :
      |f t ω-f (terminalTime n) ω| ≤ δ/4 := by
    have hbt := h.bounded t ⟨(terminalTime_mem n).1.trans ht.1.le,ht.2⟩ ω
    have hbs := h.bounded _ (terminalTime_mem n) ω
    have he := hreal t ht
    have hsq1 : (f t ω)^2 ≤ 1 := by nlinarith [abs_le.mp hbt]
    have hsq2 : (f (terminalTime n) ω)^2 ≤ 1 := by nlinarith [abs_le.mp hbs]
    have habs : |f t ω-f (terminalTime n) ω|^2 < (δ/4)^2 := by
      rw [sq_abs]
      nlinarith
    nlinarith [abs_nonneg (f t ω-f (terminalTime n) ω)]
  have hUb : |U ω-f (terminalTime n) ω| ≤ δ/4 := by
    apply le_of_tendsto ((hseqω.2.sub_const _).abs)
    have hev : ∀ᶠ k in atTop, terminalTime k ∈ Ioo (terminalTime n) 1 :=
      terminalTime_tendsto.eventually (Ioo_mem_nhdsLT (terminalTime_mem n).2)
    exact hev.mono (fun k hk ↦ hbound _ hk)
  filter_upwards [Ioo_mem_nhdsLT (terminalTime_mem n).2] with t ht
  rw [Real.dist_eq]
  have hh := abs_add_le (f t ω-f (terminalTime n) ω) (f (terminalTime n) ω-U ω)
  have hh' := hbound t ht
  have hUb' : |f (terminalTime n) ω-U ω| ≤ δ/4 := by simpa only [abs_sub_comm] using hUb
  have heq : f t ω-U ω = (f t ω-f (terminalTime n) ω)+(f (terminalTime n) ω-U ω) := by ring
  rw [heq]
  linarith

lemma UnitMomentMartingale.terminal_square
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧
      Tendsto (fun n ↦ f (terminalTime n) ω) atTop (𝓝 (U ω))) :
    ∀ᵐ ω ∂μ, (U ω)^2 = 1 := by
  have hU2i : Integrable (fun ω ↦ (U ω)^2) μ :=
    Integrable.of_bound ((hUm.mono (ℱ.le 1)).pow 2).aestronglyMeasurable 1
      (hU.mono (fun ω hω ↦ by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        nlinarith [abs_le.mp hω.1]))
  have ht := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n ω ↦ (f (terminalTime n) ω)^2) (fun _ : Ω ↦ (1 : ℝ))
    (fun n ↦ (((h.measurable _ (terminalTime_mem n)).mono (ℱ.le _)).pow 2).aestronglyMeasurable)
    (integrable_const 1)
    (fun n ↦ Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_le.mp (h.bounded _ (terminalTime_mem n) ω)]))
    (hU.mono (fun ω hω ↦ hω.2.pow 2))
  have hi : ∫ ω, (U ω)^2 ∂μ = 1 := by
    have hh : (fun n ↦ ∫ ω, (f (terminalTime n) ω)^2 ∂μ) = terminalTime :=
      funext (fun n ↦ h.secondMoment _ (terminalTime_mem n))
    rw [hh] at ht
    exact tendsto_nhds_unique ht (tendsto_nhdsWithin_iff.mp terminalTime_tendsto).1
  have hnonneg : 0 ≤ᵐ[μ] (fun ω ↦ 1-(U ω)^2) := hU.mono (fun ω hω ↦ by
    dsimp
    nlinarith [abs_le.mp hω.1])
  have hzero : ∫ ω, 1-(U ω)^2 ∂μ = 0 := by
    rw [integral_sub (integrable_const 1) hU2i,hi]
    simp
  have he := (integral_eq_zero_iff_of_nonneg_ae hnonneg ((integrable_const 1).sub hU2i)).mp hzero
  filter_upwards [he] with ω hω
  change 1-(U ω)^2=0 at hω
  linarith

lemma UnitMomentMartingale.terminal_mean_square
    (h : UnitMomentMartingale (μ := μ) ℱ f) {U : Ω → ℝ}
    (hUm : StronglyMeasurable[ℱ 1] U)
    (hU : ∀ᵐ ω ∂μ, |U ω| ≤ 1 ∧
      Tendsto (fun t ↦ f t ω) (𝓝[<] (1 : ℝ)) (𝓝 (U ω))) :
    Tendsto (fun t ↦ ∫ ω, (f t ω-U ω)^2 ∂μ) (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ico (0 : ℝ) 1 := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ)<1 by norm_num)] with t ht
    exact ⟨ht.1.le,ht.2⟩
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := fun t ω ↦ (f t ω-U ω)^2) (f := fun _ ↦ (0 : ℝ)) (fun _ : Ω ↦ (4 : ℝ))
    (hev.mono (fun t ht ↦ ((((h.measurable t ht).mono (ℱ.le t)).sub
      (hUm.mono (ℱ.le 1))).pow 2).aestronglyMeasurable))
    (hev.mono (fun t ht ↦ hU.mono (fun ω hω ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hb := h.bounded t ht ω
      have hd : |f t ω-U ω| ≤ 2 := (abs_sub _ _).trans (by linarith [hω.1])
      nlinarith [sq_abs (f t ω-U ω),abs_nonneg (f t ω-U ω)])))
    (integrable_const 4)
    (hU.mono (fun ω hω ↦ by
      simpa only [sub_self,zero_pow (by decide : (2 : ℕ) ≠ 0)] using (hω.2.sub_const (U ω)).pow 2))
  simpa only [integral_zero] using ht

end SKValue
end

end OAI
