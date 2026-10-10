import OAI.MeasureTheory.SelfSimilar.LocalEntropy

namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace EntropyRateDimension
namespace LocalMass

theorem restrict_le_hausdorff (μ : Measure ℝ) (E : Set ℝ) {a R : ℝ}
    (_ha : 0 ≤ a) (hR : 0 < R)
    (hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
      μ (closedBall x r) ≤ (ENNReal.ofReal r)^a) :
    μ.restrict E ≤ Measure.hausdorffMeasure a := by
  apply Measure.le_hausdorffMeasure a (μ.restrict E) (ENNReal.ofReal (R/2))
    (ENNReal.ofReal_pos.mpr (by positivity))
  intro A hA
  have hAtop : ediam A ≠ ⊤ := ne_top_of_le_ne_top (by simp) hA
  have hdiam : diam A < R := by
    have hh := ENNReal.toReal_mono (by simp : ENNReal.ofReal (R/2) ≠ ⊤) hA
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    exact lt_of_le_of_lt hh (by linarith)
  have hcltop : ediam (closure A) ≠ ⊤ := by rwa [ediam_closure]
  by_cases hE : (closure A ∩ E).Nonempty
  · obtain ⟨x,hxA,hxE⟩ := hE
    have hh : ∀ r : ℝ, diam A < r → r < R →
        (μ.restrict E) A ≤ (ENNReal.ofReal r)^a := by
      intro r hdr hrR
      have hr : 0 < r := lt_of_le_of_lt (diam_nonneg) hdr
      calc
        (μ.restrict E) A ≤ (μ.restrict E) (closure A) := measure_mono subset_closure
        _ = μ (closure A ∩ E) := Measure.restrict_apply isClosed_closure.measurableSet
        _ ≤ μ (closedBall x r) := measure_mono (fun y hy => by
          apply mem_closedBall.mpr
          have hd := dist_le_diam_of_mem' hcltop hy.1 hxA
          rw [diam_closure] at hd
          exact hd.trans hdr.le)
        _ ≤ _ := hball x hxE r hr hrR
    have ht : Tendsto (fun r : ℝ => (ENNReal.ofReal r)^a) (𝓝[>] (diam A))
        (𝓝 ((ediam A)^a)) := by
      have he : ENNReal.ofReal (diam A)=ediam A := ENNReal.ofReal_toReal hAtop
      rw [← he]
      exact ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).tendsto _).mono_left
        nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (isOpen_Iio.mem_nhds hdiam)] with r hdr hrR
    exact hh r hdr hrR
  · have he : closure A ∩ E=∅ := Set.not_nonempty_iff_eq_empty.mp hE
    calc
      (μ.restrict E) A ≤ (μ.restrict E) (closure A) := measure_mono subset_closure
      _ = 0 := by rw [Measure.restrict_apply isClosed_closure.measurableSet,he,measure_empty]
      _ ≤ _ := bot_le

theorem positive_set_dim_ge (μ : Measure ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hlocal : ∀ᵐ x ∂μ, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      μ (closedBall x r) ≤ (ENNReal.ofReal r)^a)
    {B : Set ℝ} (hB : MeasurableSet B) (hpos : 0 < μ B) :
    ENNReal.ofReal a ≤ dimH B := by
  let E : ℕ → Set ℝ := fun n => {x | ∀ r : ℝ, 0 < r → r < 1/((n : ℝ)+1) →
      μ (closedBall x r) ≤ (ENNReal.ofReal r)^a}
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ n, E n := by
    filter_upwards [hlocal] with x hx
    obtain ⟨R,hR,hRx⟩ := hx
    obtain ⟨n,hn⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds hR)).exists
    exact mem_iUnion.mpr ⟨n,fun r hr hrn => hRx r hr (hrn.trans hn)⟩
  have hex : ∃ n, 0 < μ (B ∩ E n) := by
    by_contra! hn
    have hzero : μ (⋃ n, B ∩ E n)=0 := measure_iUnion_null (fun n => by simpa using hn n)
    have hsub : B ≤ᵐ[μ] ⋃ n, B ∩ E n := by
      filter_upwards [hae] with x hx hxB
      obtain ⟨n,hn⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨n,hxB,hn⟩
    have := measure_mono_ae hsub
    rw [hzero] at this
    exact (not_lt_of_ge this) hpos
  obtain ⟨n,hn⟩ := hex
  have hdom := restrict_le_hausdorff μ (E n) ha (by positivity : 0 < 1/((n : ℝ)+1))
    (fun x hx r hr hrR => hx r hr hrR)
  have hmass : 0 < Measure.hausdorffMeasure a B := by
    have hh := hdom B
    rw [Measure.restrict_apply hB] at hh
    exact hn.trans_le hh
  have hh := le_dimH_of_hausdorffMeasure_ne_zero (d := ⟨a,ha⟩) hmass.ne'
  convert hh using 1
  exact (ENNReal.coe_nnreal_eq ⟨a,ha⟩).symm

theorem eventual_upper_of_limit (μ : Measure ℝ) [IsFiniteMeasure μ] {x a d : ℝ}
    (hx : x ∈ μ.support) (had : a < d)
    (hlim : Tendsto (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 d)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      μ (closedBall x r) ≤ (ENNReal.ofReal r)^a := by
  have hev := hlim.eventually (lt_mem_nhds had)
  obtain ⟨R,hR,hRx⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨min R 1,lt_min hR zero_lt_one,?_⟩
  intro r hr hrR
  have hr1 : r < 1 := lt_of_lt_of_le hrR (min_le_right _ _)
  have harr : a < -Real.log (μ.real (closedBall x r)) / -Real.log r :=
    hRx ⟨by simpa [Real.dist_eq,abs_of_pos hr] using lt_of_lt_of_le hrR (min_le_left _ _),hr⟩
  have hlogr : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr hr1)
  have hh := (lt_div_iff₀ hlogr).mp harr
  have hmass : 0 < μ.real (closedBall x r) :=
    ENNReal.toReal_pos (ne_of_gt ((Measure.mem_support_iff_forall x).mp hx _
      (closedBall_mem_nhds x hr))) (measure_ne_top μ _)
  have hle : μ.real (closedBall x r) ≤ r^a := by
    rw [Real.rpow_def_of_pos hr, ← Real.exp_log hmass]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [ENNReal.ofReal_rpow_of_pos hr,← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal hle

theorem eventual_lower_of_limit (μ : Measure ℝ) [IsFiniteMeasure μ] {x e d : ℝ}
    (hx : x ∈ μ.support) (hde : d < e)
    (hlim : Tendsto (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 d)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r) := by
  have hev := hlim.eventually (gt_mem_nhds hde)
  obtain ⟨R,hR,hRx⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨min R 1,lt_min hR zero_lt_one,?_⟩
  intro r hr hrR
  have hr1 : r < 1 := lt_of_lt_of_le hrR (min_le_right _ _)
  have harr : -Real.log (μ.real (closedBall x r)) / -Real.log r < e :=
    hRx ⟨by simpa [Real.dist_eq,abs_of_pos hr] using lt_of_lt_of_le hrR (min_le_left _ _),hr⟩
  have hh := (div_lt_iff₀ (neg_pos.mpr (Real.log_neg hr hr1))).mp harr
  have hmass : 0 < μ.real (closedBall x r) :=
    ENNReal.toReal_pos (ne_of_gt ((Measure.mem_support_iff_forall x).mp hx _
      (closedBall_mem_nhds x hr))) (measure_ne_top μ _)
  rw [Real.rpow_def_of_pos hr,← Real.exp_log hmass]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem lower_dim_ge_of_limit (μ : Measure ℝ) [IsProbabilityMeasure μ] {d : ℝ}
    (hlim : ∀ᵐ x ∂μ, Tendsto
      (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r) (𝓝[>] 0) (𝓝 d)) :
    ENNReal.ofReal d ≤ lowerHausdorffDimension μ := by
  unfold lowerHausdorffDimension
  apply le_iInf
  intro B
  apply le_iInf
  intro hB
  apply le_iInf
  intro hpos
  by_cases htop : dimH B=⊤
  · rw [htop]; exact le_top
  rw [ENNReal.ofReal_le_iff_le_toReal htop]
  apply le_of_forall_lt_imp_le_of_dense
  intro a had
  by_cases ha : 0 ≤ a
  · have hh := positive_set_dim_ge μ ha (by
      filter_upwards [hlim,μ.support_mem_ae] with x hx hs
      exact eventual_upper_of_limit μ hs had hx) hB hpos
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp hh
  · exact (le_of_not_ge ha).trans ENNReal.toReal_nonneg

theorem large_uniform_mass_set (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e η : ℝ} (he : 0 ≤ e) (hη : 0 < η)
    (hlocal : ∀ᵐ x ∂μ, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ μ.real Eᶜ ≤ η ∧
      ∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
        (r/2)^e ≤ μ.real (ball x r) := by
  let E : ℕ → Set ℝ := fun n => {x | ∀ q : ℚ, 0 < (q : ℝ) →
    (q : ℝ) < 1/((n : ℝ)+1) → (q : ℝ)^e ≤ μ.real (closedBall x q)}
  have hE : ∀ n, MeasurableSet (E n) := by
    intro n
    simp only [E,Set.ofPred_forall]
    apply MeasurableSet.iInter fun q : ℚ => ?_
    apply MeasurableSet.iInter fun _ : 0 < (q : ℝ) => ?_
    apply MeasurableSet.iInter fun _ : (q : ℝ) < 1/((n : ℝ)+1) => ?_
    have hm := measurable_measure_prodMk_left (ν := μ)
      (measurableSet_le (measurable_snd.dist measurable_fst) (measurable_const (a := (q : ℝ))))
    exact measurableSet_le measurable_const hm.ennreal_toReal
  have hmono : Monotone E := by
    intro n m hnm x hx q hq hqm
    apply hx q hq
    exact hqm.trans_le (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1))
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ n, E n := by
    filter_upwards [hlocal] with x hx
    obtain ⟨R,hR,hRx⟩ := hx
    obtain ⟨n,hn⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds hR)).exists
    exact mem_iUnion.mpr ⟨n,fun q hq hqn => hRx q hq (hqn.trans hn)⟩
  have hzero : μ (⋂ n, (E n)ᶜ)=0 := by
    rw [← compl_iUnion]
    exact ae_iff.mp hae
  have ht : Tendsto (fun n => μ ((E n)ᶜ)) atTop (𝓝 0) := by
    rw [← hzero]
    exact tendsto_measure_iInter_atTop (fun n => (hE n).compl.nullMeasurableSet)
      (fun n m hnm => compl_subset_compl.mpr (hmono hnm)) ⟨0,measure_ne_top μ _⟩
  have htR : Tendsto (fun n => μ.real ((E n)ᶜ)) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero,Function.comp_def,Measure.real] using (ENNReal.continuousAt_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp ht
  obtain ⟨n,hn⟩ := (htR.eventually (gt_mem_nhds hη)).exists
  refine ⟨E n,hE n,hn.le,1/((n : ℝ)+1),by positivity,?_⟩
  intro x hx r hr hrR
  obtain ⟨q,hq1,hq2⟩ := exists_rat_btwn (by linarith : r/2 < r)
  have hmass := hx q (lt_trans (by positivity) hq1) (hq2.trans hrR)
  have hsub : closedBall x (q : ℝ) ⊆ ball x r := fun y hy =>
    mem_ball.mpr ((mem_closedBall.mp hy).trans_lt hq2)
  exact (Real.rpow_le_rpow (by positivity) hq1.le he).trans
    (hmass.trans (measureReal_mono hsub))

end LocalMass
end EntropyRateDimension

end

end OAI
