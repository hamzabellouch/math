import OAI.MeasureTheory.SelfSimilar.InvariantLaw

namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace EntropyRateDimension
namespace BallRatios

theorem exists_small_ratio_bound : ∃ N : ℕ, ∀ (μ ν : Measure ℝ) (t : ℝ≥0∞)
    (E : Set ℝ),
    (∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ν (closedBall x r) ≤ t*μ (closedBall x r)) →
    ν E ≤ N*t*μ univ := by
  classical
  obtain ⟨N,τ,hτ,hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := ℝ)
  refine ⟨N, ?_⟩
  intro μ ν t E hE
  choose r hr hr1 hrat using fun x : E => hE x.val x.property
  let q : Besicovitch.BallPackage E ℝ :=
    { c := Subtype.val, r := r, rpos := hr, r_bound := 1, r_le := hr1 }
  obtain ⟨s,hd,hcover⟩ := Besicovitch.exist_disjoint_covering_families hτ hN q
  have hcnt : ∀ i, (s i).Countable := by
    intro i
    apply (hd i).countable_of_nonempty_interior
    intro x hx
    exact ⟨x.val, ball_subset_interior_closedBall (mem_ball_self (hr x))⟩
  have hb : ∀ i, ν (⋃ x ∈ s i, ball (q.c x) (q.r x)) ≤ t*μ univ := by
    intro i
    calc
      _ ≤ ∑' x : s i, ν (closedBall (q.c x.val) (q.r x.val)) := by
        apply le_trans (measure_biUnion_le ν (hcnt i) _)
        exact ENNReal.tsum_le_tsum fun x => measure_mono ball_subset_closedBall
      _ ≤ ∑' x : s i, t*μ (closedBall (q.c x.val) (q.r x.val)) :=
        ENNReal.tsum_le_tsum fun x => hrat x.val
      _ = t * μ (⋃ x ∈ s i, closedBall (q.c x) (q.r x)) := by
        rw [ENNReal.tsum_mul_left, measure_biUnion (hcnt i) (hd i)
          (fun _ _ => measurableSet_closedBall)]
      _ ≤ t*μ univ := mul_le_mul' le_rfl (measure_mono (subset_univ _))
  calc
    ν E ≤ ν (⋃ i, ⋃ x ∈ s i, ball (q.c x) (q.r x)) := by
      apply measure_mono
      intro x hx
      exact hcover ⟨⟨x,hx⟩,rfl⟩
    _ ≤ ∑ i : Fin N, ν (⋃ x ∈ s i, ball (q.c x) (q.r x)) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin N, t*μ univ := Finset.sum_le_sum fun i _ => hb i
    _ = N*t*μ univ := by simp [mul_assoc]

abbrev Radius := {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) ≤ 1}

noncomputable def maximal (μ ν : Measure ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ q : Radius, μ (closedBall x (q.val : ℝ)) / ν (closedBall x (q.val : ℝ))

theorem measurable_ball_mass (μ : Measure ℝ) [SFinite μ] (r : ℝ) :
    Measurable (fun x : ℝ => μ (closedBall x r)) := by
  have hs : MeasurableSet {p : ℝ × ℝ | dist p.2 p.1 ≤ r} :=
    measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
  exact measurable_measure_prodMk_left hs

theorem maximal_measurable (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    Measurable (maximal μ ν) := by
  apply Measurable.iSup
  intro q
  exact (measurable_ball_mass μ _).div (measurable_ball_mass ν _)

theorem maximal_tail {N : ℕ}
    (hN : ∀ (μ ν : Measure ℝ) (t : ℝ≥0∞) (E : Set ℝ),
      (∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ν (closedBall x r) ≤ t*μ (closedBall x r)) →
      ν E ≤ N*t*μ univ)
    (μ ν : Measure ℝ) [IsFiniteMeasure ν] (a : ℝ≥0∞) (ha : a ≠ 0) (hat : a ≠ ⊤) :
    ν {x | a < maximal μ ν x} ≤ N * a⁻¹ * μ univ := by
  apply hN
  intro x hx
  obtain ⟨q,hq⟩ : ∃ q : Radius, a < μ (closedBall x (q.val : ℝ)) /
      ν (closedBall x (q.val : ℝ)) := by
    simpa only [Set.mem_ofPred_eq, maximal, lt_iSup_iff] using hx
  refine ⟨q.val,q.property.1,q.property.2,?_⟩
  have hh := (ENNReal.lt_div_iff_mul_lt (Or.inr hat)
    (Or.inl (measure_ne_top ν _))).mp hq
  have := (ENNReal.le_div_iff_mul_le (Or.inl ha) (Or.inl hat)).mpr
    (show ν (closedBall x (q.val : ℝ)) * a ≤ μ (closedBall x (q.val : ℝ)) by
      simpa only [mul_comm] using hh.le)
  simpa only [div_eq_mul_inv,mul_comm] using this

theorem maximal_finite_ae (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∀ᵐ x ∂ν, maximal μ ν x ≠ ⊤ := by
  obtain ⟨N,hN⟩ := exists_small_ratio_bound
  apply ae_iff.mpr
  simp only [not_not]
  apply le_antisymm _ bot_le
  have hlim : Tendsto (fun n : ℕ => (N : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ * μ univ)
      atTop (𝓝 0) := by
    have hh := ENNReal.Tendsto.const_mul ENNReal.tendsto_nat_nhds_top.inv
      (Or.inr (show (N : ℝ≥0∞) ≠ ⊤ by simp))
    have hf := ENNReal.Tendsto.mul_const hh (Or.inr (measure_ne_top μ univ))
    simpa using hf
  apply ge_of_tendsto hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  calc
    ν {x | maximal μ ν x = ⊤} ≤ ν {x | (n : ℝ≥0∞) < maximal μ ν x} := by
      apply measure_mono
      intro x (hx : maximal μ ν x = ⊤)
      change (n : ℝ≥0∞) < maximal μ ν x
      rw [hx]
      exact ENNReal.natCast_lt_top n
    _ ≤ _ := maximal_tail hN μ ν n (by exact_mod_cast hn.ne') (by simp)

noncomputable def logEnvelope (μ ν : Measure ℝ) (x : ℝ) : ℝ :=
  max 0 (Real.log (maximal μ ν x).toReal)

theorem logEnvelope_nonneg (μ ν : Measure ℝ) (x : ℝ) : 0 ≤ logEnvelope μ ν x :=
  le_max_left _ _

theorem logEnvelope_measurable (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    Measurable (logEnvelope μ ν) :=
  measurable_const.max (maximal_measurable μ ν).ennreal_toReal.log

theorem logEnvelope_tail {N : ℕ}
    (hN : ∀ (μ ν : Measure ℝ) (t : ℝ≥0∞) (E : Set ℝ),
      (∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ν (closedBall x r) ≤ t*μ (closedBall x r)) →
      ν E ≤ N*t*μ univ)
    (μ ν : Measure ℝ) [IsFiniteMeasure ν] {t : ℝ} (ht : 0 ≤ t) :
    ν {x | t < logEnvelope μ ν x} ≤
      (N : ℝ≥0∞)*μ univ*ENNReal.ofReal (Real.exp (-t)) := by
  calc
    _ ≤ ν {x | ENNReal.ofReal (Real.exp t) < maximal μ ν x} := by
      apply measure_mono
      intro x hx
      have hh : t < Real.log (maximal μ ν x).toReal :=
        (lt_max_iff.mp hx).resolve_left (not_lt_of_ge ht)
      have hp : 0 < (maximal μ ν x).toReal := by
        apply lt_of_le_of_ne ENNReal.toReal_nonneg
        intro he
        simp [← he] at hh
        linarith
      have he := (Real.lt_log_iff_exp_lt hp).mp hh
      exact ((ENNReal.ofReal_lt_ofReal_iff hp).mpr he).trans_le ENNReal.ofReal_toReal_le
    _ ≤ (N : ℝ≥0∞)*(ENNReal.ofReal (Real.exp t))⁻¹*μ univ :=
      maximal_tail hN μ ν _ (by simp [Real.exp_pos]) (by simp)
    _ = _ := by rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos t)]; ring

theorem logEnvelope_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (logEnvelope μ ν) ν := by
  obtain ⟨N,hN⟩ := exists_small_ratio_bound
  refine ⟨(logEnvelope_measurable μ ν).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (logEnvelope_nonneg μ ν)),
    lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall (logEnvelope_nonneg μ ν))
      (logEnvelope_measurable μ ν).aemeasurable]
  calc
    _ ≤ ∫⁻ t : ℝ in Ioi 0, (N : ℝ≥0∞)*μ univ*ENNReal.ofReal (Real.exp (-t)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact logEnvelope_tail hN μ ν ht.le
    _ = (N : ℝ≥0∞)*μ univ*∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-t)) :=
      lintegral_const_mul _ (by fun_prop)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (measure_lt_top μ _))
      ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall
        (fun t : ℝ => (Real.exp_pos (-t)).le))).mp
          (integrableOn_exp_neg_Ioi 0).hasFiniteIntegral)

theorem tendsto_ball_mass_right (μ : Measure ℝ) [IsFiniteMeasure μ] (x r : ℝ) :
    Tendsto (fun t => μ (closedBall x t)) (𝓝[>] r) (𝓝 (μ (closedBall x r))) := by
  have h := tendsto_measure_biInter_gt (μ := μ) (a := r)
    (s := fun t : ℝ => closedBall x t)
    (fun _ _ => measurableSet_closedBall.nullMeasurableSet)
    (fun _ _ _ h => closedBall_subset_closedBall h)
    ⟨r+1,by linarith,measure_ne_top μ _⟩
  simpa only [biInter_gt_closedBall,Function.comp_def] using h

theorem ratio_le_maximal (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (x : ℝ) (hx : x ∈ ν.support) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    μ (closedBall x r) / ν (closedBall x r) ≤ maximal μ ν x := by
  obtain ⟨q,_hq,hqr,hql⟩ := (Rat.denseRange_cast (𝕜 := ℝ)).exists_seq_strictAnti_tendsto_of_lt
    Rat.cast_strictMono.monotone hr1
  have ht : Tendsto (fun n => (q n : ℝ)) atTop (𝓝[>] r) :=
    tendsto_nhdsWithin_iff.mpr ⟨hql,Eventually.of_forall fun n => (hqr n).1⟩
  have hp : ν (closedBall x r) ≠ 0 :=
    ne_of_gt ((Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr))
  have hlim := ENNReal.Tendsto.div ((tendsto_ball_mass_right μ x r).comp ht)
    (Or.inr hp) ((tendsto_ball_mass_right ν x r).comp ht) (Or.inl (measure_ne_top ν _))
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun n =>
    le_iSup (fun q : Radius => μ (closedBall x (q.val : ℝ)) / ν (closedBall x (q.val : ℝ)))
      ⟨q n,lt_trans hr (hqr n).1,(hqr n).2.le⟩

noncomputable def logRatio (μ ν : Measure ℝ) (x r : ℝ) : ℝ :=
  Real.log (μ (closedBall x r) / ν (closedBall x r)).toReal

theorem logRatio_measurable (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    Measurable (fun p : ℝ × ℝ => logRatio μ ν p.1 p.2) := by
  have hm (κ : Measure ℝ) [SFinite κ] :
      Measurable (fun p : ℝ × ℝ => κ (closedBall p.1 p.2)) := by
    have hs : MeasurableSet {z : (ℝ × ℝ) × ℝ | dist z.2 z.1.1 ≤ z.1.2} :=
      measurableSet_le (measurable_snd.dist (measurable_fst.fst)) (measurable_fst.snd)
    exact measurable_measure_prodMk_left hs
  exact ((hm μ).div (hm ν)).ennreal_toReal.log

theorem logRatio_bounds (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν ≤ μ) : ∀ᵐ x ∂ν, ∀ r : ℝ, 0 < r → r < 1 →
      0 ≤ logRatio μ ν x r ∧ logRatio μ ν x r ≤ logEnvelope μ ν x := by
  filter_upwards [ν.support_mem_ae,maximal_finite_ae μ ν] with x hx hmax
  intro r hr hr1
  have hp := (Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr)
  have hge : 1 ≤ μ (closedBall x r) / ν (closedBall x r) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hp.ne') (Or.inl (measure_ne_top ν _))).mpr
    simpa only [one_mul] using hν (closedBall x r)
  have htop := ne_top_of_le_ne_top hmax (ratio_le_maximal μ ν x hx hr hr1)
  have hreal : 1 ≤ (μ (closedBall x r) / ν (closedBall x r)).toReal := by
    exact_mod_cast (ENNReal.toReal_mono htop hge)
  refine ⟨Real.log_nonneg hreal,?_⟩
  apply le_trans _ (le_max_right 0 _)
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one hreal)
  exact ENNReal.toReal_mono hmax (ratio_le_maximal μ ν x hx hr hr1)

theorem ae_logRatio_limit (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν ≤ μ) : ∀ᵐ x ∂ν,
      1 ≤ (μ.rnDeriv ν x).toReal ∧
      Tendsto (logRatio μ ν x) (𝓝[>] 0) (𝓝 (Real.log (μ.rnDeriv ν x).toReal)) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ ν, μ.rnDeriv_ne_top ν,
    ν.support_mem_ae] with x hlim htop hx
  have hge : 1 ≤ μ.rnDeriv ν x := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have hp := (Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr)
    apply (ENNReal.le_div_iff_mul_le (Or.inl hp.ne') (Or.inl (measure_ne_top ν _))).mpr
    simpa only [one_mul] using hν (closedBall x r)
  have hreal : 1 ≤ (μ.rnDeriv ν x).toReal := by
    simpa using ENNReal.toReal_mono htop hge
  refine ⟨hreal,?_⟩
  exact (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one hreal))).tendsto.comp
    ((ENNReal.continuousAt_toReal htop).tendsto.comp hlim)

end BallRatios
end EntropyRateDimension

end

end OAI
