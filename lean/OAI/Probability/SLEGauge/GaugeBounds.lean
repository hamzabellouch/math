import Mathlib
import OAI.Probability.SLE.MomentGauge

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Target

open scoped ContinuousMapZero

end SLEExactGauge.Target

 

 

namespace SLEExactGauge.BrownianLaw
open SLEExactGauge.Target
open ProbabilityTheory Function
open scoped ContinuousMapZero

instance : PolishSpace Driver := ContinuousMapZero.isClosedEmbedding_toContinuousMap.polishSpace

def code (b : Driver) : ℚ → ℝ := fun q => b (Real.toNNReal (q:ℝ))

lemma measurable_code : Measurable code :=
  Measurable.of_eval fun _ => (continuous_eval_const _).measurable

lemma dense_rational_time : DenseRange (fun q : ℚ => Real.toNNReal (q:ℝ)) := by
  have hd : Surjective Real.toNNReal := fun x => ⟨(x:ℝ),Real.toNNReal_coe⟩
  exact hd.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal

lemma code_injective : Injective code := by
  intro b c h
  apply ContinuousMapZero.ext
  have he := dense_rational_time.equalizer (map_continuous b) (map_continuous c) h
  exact congrFun he

lemma code_embedding : MeasurableEmbedding code := measurable_code.measurableEmbedding code_injective

lemma evaluation_law_unique {W V : Measure Driver}
    (hW : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) W)
    (hV : IsBrownianReal (fun (s : ℝ≥0) (b : Driver) => b s) V) : W = V := by
  let ev : Driver → (ℝ≥0 → ℝ) := fun b => b
  have mev : Measurable ev := Measurable.of_eval fun time => (continuous_eval_const time).measurable
  have hw : IsProjectiveLimit (W.map ev) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map I.measurable_restrict mev]
    exact (hW.hasLaw I).map_eq
  have hv : IsProjectiveLimit (V.map ev) BrownianReal.projectiveFamily := by
    intro I
    rw [Measure.map_map I.measurable_restrict mev]
    exact (hV.hasLaw I).map_eq
  have he := hw.unique hv
  have mr : Measurable (fun f : ℝ≥0 → ℝ => fun q : ℚ => f (Real.toNNReal (q:ℝ))) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  have hc := congrArg (Measure.map (fun f : ℝ≥0 → ℝ => fun q : ℚ => f (Real.toNNReal (q:ℝ)))) he
  rw [Measure.map_map mr mev, Measure.map_map mr mev] at hc
  exact code_embedding.map_injective hc

end SLEExactGauge.BrownianLaw

namespace SLEExactGauge.Deterministic

open SLEExactGauge.Target

 

def diameterCost (h : ℝ → ℝ) (r : ℝ≥0∞) : ℝ≥0∞ :=
  if r = ∞ then ∞ else ENNReal.ofReal (h r.toReal)

lemma diameterCost_zero {h : ℝ → ℝ} (h0 : h 0 = 0) :
    diameterCost h 0 = 0 := by
  simp [diameterCost, h0]

lemma gauge_nonneg {h : ℝ → ℝ} (hh : IsHausdorffGauge h)
    {r : ℝ} (hr : 0 ≤ r) : 0 ≤ h r := by
  rw [← hh.2.2.1]
  exact hh.2.1 (by simp) hr hr

 

theorem hausdorff_countable_covers {h : ℝ → ℝ} (h0 : h 0 = 0) (E : Set ℂ) :
    hausdorff h E =
      ⨆ (δ : ℝ≥0∞) (_ : 0 < δ),
        ⨅ (U : ℕ → Set ℂ) (_ : E ⊆ ⋃ n, U n) (_ : ∀ n, Metric.ediam (U n) ≤ δ),
          ∑' n, diameterCost h (Metric.ediam (U n)) := by
  change OuterMeasure.mkMetric (diameterCost h) E = _
  rw [OuterMeasure.coe_mkMetric, Measure.mkMetric_apply]
  congr 1 with δ
  congr 1 with hδ
  congr 1 with U
  congr 1 with hEU
  congr 1 with hU
  apply tsum_congr
  intro n
  by_cases hn : (U n).Nonempty
  · simp [hn]
  · have hempty : U n = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [hempty, diameterCost_zero h0]

 
theorem hausdorff_tendsto_content (h : ℝ → ℝ) (E : Set ℂ) :
    Tendsto
      (fun δ : ℝ≥0∞ =>
        OuterMeasure.mkMetric'.pre (fun U : Set ℂ => diameterCost h (Metric.ediam U)) δ E)
      (𝓝[>] 0) (𝓝 (hausdorff h E)) :=
  OuterMeasure.mkMetric'.tendsto_pre _ _

 

theorem mass_bound {h : ℝ → ℝ} {ν : OuterMeasure ℂ} {δ c : ℝ≥0∞}
    (hδ : 0 < δ) (hc0 : c ≠ 0) (hc : c ≠ ∞)
    (hν : ∀ U : Set ℂ, Metric.ediam U ≤ δ →
      ν U ≤ c * diameterCost h (Metric.ediam U)) :
    ν ≤ c • hausdorff h := by
  have hm : ν ≤ OuterMeasure.mkMetric (c • diameterCost h) :=
    OuterMeasure.le_mkMetric _ ν δ hδ hν
  change ν ≤ c • OuterMeasure.mkMetric (diameterCost h)
  simpa only [OuterMeasure.mkMetric_smul _ hc hc0] using hm

 

theorem hausdorff_pos_of_mass_bound {h : ℝ → ℝ} {ν : OuterMeasure ℂ}
    {δ c : ℝ≥0∞} {E : Set ℂ}
    (hδ : 0 < δ) (hc0 : c ≠ 0) (hc : c ≠ ∞)
    (hν : ∀ U : Set ℂ, Metric.ediam U ≤ δ →
      ν U ≤ c * diameterCost h (Metric.ediam U))
    (hE : 0 < ν E) : 0 < hausdorff h E := by
  have H := mass_bound hδ hc0 hc hν E
  by_contra hn
  have hz : hausdorff h E = 0 := le_antisymm (not_lt.mp hn) zero_le
  have hle : ν E ≤ 0 := by simpa [smul_apply, hz] using H
  exact hE.not_ge hle

 

theorem hausdorff_le_liminf_cost {ι : ℕ → Type*} [∀ n, Countable (ι n)]
    (h : ℝ → ℝ) (E : Set ℂ) (r : ℕ → ℝ≥0∞)
    (hr : Tendsto r atTop (𝓝 0)) (U : ∀ n, ι n → Set ℂ)
    (hdiam : ∀ᶠ n in atTop, ∀ i, Metric.ediam (U n i) ≤ r n)
    (hcover : ∀ᶠ n in atTop, E ⊆ ⋃ i, U n i) :
    hausdorff h E ≤ liminf (fun n => ∑' i, diameterCost h (Metric.ediam (U n i))) atTop := by
  change OuterMeasure.mkMetric (diameterCost h) E ≤ _
  rw [OuterMeasure.coe_mkMetric]
  exact Measure.mkMetric_le_liminf_tsum E r hr U hdiam hcover _

section Intervals

variable {X Ω : Type*}

 

theorem all_real_intervals_of_rational (ν : OuterMeasure X) (γ : ℝ → X)
    (H : ∀ p q : ℚ, 0 < p → p < q →
      0 < ν (γ '' Icc (p : ℝ) (q : ℝ)) ∧
        ν (γ '' Icc (p : ℝ) (q : ℝ)) < ∞) :
    ∀ s t : ℝ, 0 < s → s < t →
      0 < ν (γ '' Icc s t) ∧ ν (γ '' Icc s t) < ∞ := by
  intro s t hs hst
  obtain ⟨p, hsp, hpt⟩ := exists_rat_btwn hst
  obtain ⟨q, hpq, hqt⟩ := exists_rat_btwn hpt
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hs.trans hsp
  have hpq' : p < q := by exact_mod_cast hpq
  have hinner : γ '' Icc (p : ℝ) (q : ℝ) ⊆ γ '' Icc s t :=
    image_mono (Icc_subset_Icc hsp.le hqt.le)
  have hpos := (H p q hp0 hpq').1.trans_le (ν.mono hinner)
  obtain ⟨u, hu0, hus⟩ := exists_rat_btwn hs
  obtain ⟨v, htv, _⟩ := exists_rat_btwn (lt_add_one t)
  have hu0' : (0 : ℚ) < u := by exact_mod_cast hu0
  have huv : u < v := by exact_mod_cast hus.trans (hst.trans htv)
  have houter : γ '' Icc s t ⊆ γ '' Icc (u : ℝ) (v : ℝ) :=
    image_mono (Icc_subset_Icc hus.le htv.le)
  exact ⟨hpos, (ν.mono houter).trans_lt (H u v hu0' huv).2⟩

 

theorem ae_all_real_intervals_iff_rational [MeasurableSpace Ω]
    (P : Measure Ω) (ν : OuterMeasure X) (γ : Ω → ℝ → X) :
    (∀ᵐ ω ∂P, ∀ s t : ℝ, 0 < s → s < t →
      0 < ν (γ ω '' Icc s t) ∧ ν (γ ω '' Icc s t) < ∞) ↔
    (∀ p q : ℚ, 0 < p → p < q →
      ∀ᵐ ω ∂P, 0 < ν (γ ω '' Icc (p : ℝ) (q : ℝ)) ∧
        ν (γ ω '' Icc (p : ℝ) (q : ℝ)) < ∞) := by
  constructor
  · intro H p q hp hpq
    filter_upwards [H] with ω hω
    exact hω p q (by exact_mod_cast hp) (by exact_mod_cast hpq)
  · intro H
    have H' : ∀ᵐ ω ∂P, ∀ p q : ℚ, 0 < p → p < q →
        0 < ν (γ ω '' Icc (p : ℝ) (q : ℝ)) ∧
          ν (γ ω '' Icc (p : ℝ) (q : ℝ)) < ∞ := by
      simpa only [ae_all_iff] using H
    filter_upwards [H'] with ω hω
    exact all_real_intervals_of_rational ν (γ ω) hω

end Intervals
end SLEExactGauge.Deterministic
end
end
 

 
section
 

noncomputable section
open Set Filter Topology
namespace SLEExactGauge.QuadraticGauge

 

def entry (d b ρ r : ℝ) : ℝ := b * ρ ^ d * max 1 ((r / ρ)^2)

 
def gauge {ι : Type*} (d : ℝ) (b ρ : ι → ℝ) (r : ℝ) : ℝ :=
  ⨅ i, entry d (b i) (ρ i) r

lemma entry_nonneg {d b ρ r : ℝ} (hb : 0 ≤ b) (hρ : 0 < ρ) :
    0 ≤ entry d b ρ r := by
  unfold entry
  positivity

lemma base_le_entry {d b ρ r : ℝ} (hb : 0 ≤ b) (hρ : 0 < ρ) :
    b * ρ^d ≤ entry d b ρ r := by
  unfold entry
  exact le_mul_of_one_le_right (mul_nonneg hb (Real.rpow_nonneg hρ.le _)) (le_max_left _ _)

lemma entry_eq_base {d b ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r) (hrρ : r ≤ ρ) :
    entry d b ρ r = b * ρ^d := by
  have hq : 0 ≤ r/ρ := div_nonneg hr hρ.le
  have hq1 : r/ρ ≤ 1 := (div_le_one hρ).mpr hrρ
  have hs : (r/ρ)^2 ≤ 1 := by nlinarith
  simp only [entry,max_eq_left hs,mul_one]

lemma entry_mono {d b ρ : ℝ} (hb : 0 ≤ b) (hρ : 0 < ρ) :
    MonotoneOn (entry d b ρ) (Ici 0) := by
  intro r hr s hs hrs
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hb (Real.rpow_nonneg hρ.le _))
  apply max_le_max le_rfl
  exact pow_le_pow_left₀ (div_nonneg hr hρ.le) (div_le_div_of_nonneg_right hrs hρ.le) 2

lemma entry_scale {d b ρ C r : ℝ} (hb : 0 ≤ b) (hρ : 0 < ρ) (hC : 1 ≤ C) :
    entry d b ρ (C*r) ≤ C^2 * entry d b ρ r := by
  have hC2 : 1 ≤ C^2 := by nlinarith
  have ht : max 1 ((C*r/ρ)^2) ≤ C^2 * max 1 ((r/ρ)^2) := by
    apply max_le
    · exact hC2.trans (le_mul_of_one_le_right (sq_nonneg C) (le_max_left _ _))
    · calc
        (C*r/ρ)^2 = C^2 * (r/ρ)^2 := by ring
        _ ≤ C^2 * max 1 ((r/ρ)^2) := mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg C)
  have hm := mul_le_mul_of_nonneg_left ht (mul_nonneg hb (Real.rpow_nonneg hρ.le d))
  dsimp only [entry]
  nlinarith only [hm]

lemma power_le_entry {d b ρ r c : ℝ} (hd : 0 ≤ d) (hd2 : d ≤ 2)
    (hc : 0 ≤ c) (hcb : c ≤ b) (hρ : 0 < ρ) (hr : 0 < r) :
    c*r^d ≤ entry d b ρ r := by
  have hb : 0 ≤ b := hc.trans hcb
  by_cases hrρ : r ≤ ρ
  · calc
      c*r^d ≤ b*ρ^d := mul_le_mul hcb (Real.rpow_le_rpow hr.le hrρ hd)
        (Real.rpow_nonneg hr.le _) hb
      _ ≤ entry d b ρ r := base_le_entry hb hρ
  · have hρr : ρ ≤ r := (lt_of_not_ge hrρ).le
    have he : (r/ρ)^d ≤ (r/ρ)^2 := by
      simpa only [Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_le ((one_le_div hρ).mpr hρr) hd2
    have hh : r^d ≤ ρ^d * (r/ρ)^2 := by
      rw [Real.div_rpow hr.le hρ.le] at he
      have hρd : 0 < ρ^d := Real.rpow_pos_of_pos hρ _
      nlinarith [(div_le_iff₀ hρd).mp he]
    calc
      c*r^d ≤ b*(ρ^d * (r/ρ)^2) := mul_le_mul hcb hh (Real.rpow_nonneg hr.le _) hb
      _ ≤ entry d b ρ r := by
        unfold entry
        nlinarith only [mul_le_mul_of_nonneg_left (le_max_right 1 ((r/ρ)^2))
          (mul_nonneg hb (Real.rpow_nonneg hρ.le d))]

section Envelope
variable {ι : Type*} [Nonempty ι] {d : ℝ} {b ρ : ι → ℝ}
variable (hb : ∀ i, 0 ≤ b i) (hρ : ∀ i, 0 < ρ i)
include hb hρ

omit [Nonempty ι] in
lemma entry_bddBelow (r : ℝ) : BddBelow (range (fun i => entry d (b i) (ρ i) r)) := by
  refine ⟨0,?_⟩
  rintro _ ⟨i,rfl⟩
  exact entry_nonneg (hb i) (hρ i)

lemma gauge_nonneg (r : ℝ) : 0 ≤ gauge d b ρ r :=
  le_ciInf (fun i => entry_nonneg (hb i) (hρ i))

omit [Nonempty ι] in
lemma gauge_le_entry (r : ℝ) (i : ι) : gauge d b ρ r ≤ entry d (b i) (ρ i) r :=
  ciInf_le (entry_bddBelow hb hρ r) i

omit [Nonempty ι] in
lemma gauge_mono : MonotoneOn (gauge d b ρ) (Ici 0) := by
  intro r hr s hs hrs
  exact ciInf_mono (entry_bddBelow hb hρ r) (fun i => entry_mono (hb i) (hρ i) hr hs hrs)

lemma gauge_scale {C r : ℝ} (hC : 1 ≤ C) :
    gauge d b ρ (C*r) ≤ C^2 * gauge d b ρ r := by
  have hCp : 0 < C^2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hC)
  rw [mul_comm (C^2)]
  apply (div_le_iff₀ hCp).mp
  apply le_ciInf
  intro i
  apply (div_le_iff₀ hCp).mpr
  exact (gauge_le_entry hb hρ (C*r) i).trans (by
    simpa only [mul_comm] using entry_scale (hb i) (hρ i) hC)

lemma gauge_comparison {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    gauge d b ρ r ≤ max 1 ((r/s)^2) * gauge d b ρ s := by
  by_cases hrs : r ≤ s
  · have hh : (r/s)^2 ≤ 1 := by
      have hq : 0 ≤ r/s := div_nonneg hr.le hs.le
      have hq1 : r/s ≤ 1 := (div_le_one hs).mpr hrs
      nlinarith
    rw [max_eq_left hh,one_mul]
    exact gauge_mono hb hρ hr.le hs.le hrs
  · have hq : 1 ≤ r/s := (one_le_div hs).mpr (le_of_not_ge hrs)
    have hq2 : 1 ≤ (r/s)^2 := by nlinarith
    rw [max_eq_right hq2]
    convert gauge_scale (d := d) hb hρ (r := s) hq using 1
    field_simp

lemma gauge_continuousAt {r : ℝ} (hr : 0 < r) : ContinuousAt (gauge d b ρ) r := by
  have hu : ContinuousAt (fun s : ℝ => max 1 ((s/r)^2) * gauge d b ρ r) r := by
    fun_prop
  have hl : ContinuousAt (fun s : ℝ => gauge d b ρ r / max 1 ((r/s)^2)) r := by
    apply ContinuousAt.div continuousAt_const
    · apply ContinuousAt.sup continuousAt_const
      exact ((continuousAt_const.div continuousAt_id hr.ne').pow 2)
    · exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hu' : Tendsto (fun s : ℝ => max 1 ((s/r)^2) * gauge d b ρ r) (𝓝 r)
      (𝓝 (gauge d b ρ r)) := by simpa [hr.ne'] using hu.tendsto
  have hl' : Tendsto (fun s : ℝ => gauge d b ρ r / max 1 ((r/s)^2)) (𝓝 r)
      (𝓝 (gauge d b ρ r)) := by simpa [hr.ne'] using hl.tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl' hu'
  · filter_upwards [Ioi_mem_nhds hr] with s hs
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr
      (by simpa only [mul_comm] using gauge_comparison hb hρ hr hs)
  · filter_upwards [Ioi_mem_nhds hr] with s hs
    exact gauge_comparison hb hρ hs hr

lemma gauge_zero (hsmall : ∀ ε : ℝ, 0 < ε → ∃ i, b i*(ρ i)^d < ε) :
    gauge d b ρ 0 = 0 := by
  apply le_antisymm _ (gauge_nonneg hb hρ 0)
  by_contra! hp
  obtain ⟨i,hi⟩ := hsmall _ hp
  have he := gauge_le_entry (d := d) hb hρ 0 i
  rw [entry_eq_base (hρ i) le_rfl (hρ i).le] at he
  exact (not_lt_of_ge he) hi

lemma gauge_continuousWithinAt_zero
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ i, b i*(ρ i)^d < ε) :
    ContinuousWithinAt (gauge d b ρ) (Ici 0) 0 := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨i,hi⟩ := hsmall ε hε
  refine ⟨ρ i,hρ i,?_⟩
  intro r hr hrd
  change 0 ≤ r at hr
  have hrρ : r ≤ ρ i := by
    exact le_of_lt (by simpa only [Real.dist_eq, sub_zero,abs_of_nonneg hr] using hrd)
  rw [gauge_zero hb hρ hsmall,Real.dist_eq,sub_zero,abs_of_nonneg (gauge_nonneg hb hρ r)]
  exact (gauge_le_entry hb hρ r i).trans_lt (by
    rwa [entry_eq_base (hρ i) hr hrρ])

 

theorem isHausdorffGauge (hd : 0 ≤ d) (hd2 : d ≤ 2)
    {c : ℝ} (hc : 0 < c) (hcb : ∀ i, c ≤ b i)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ i, b i*(ρ i)^d < ε) :
    Target.IsHausdorffGauge (gauge d b ρ) := by
  refine ⟨?_,gauge_mono hb hρ,gauge_zero hb hρ hsmall,?_⟩
  · intro r hr
    rcases (show 0 ≤ r from hr).eq_or_lt with he | hp
    · subst r
      exact gauge_continuousWithinAt_zero hb hρ hsmall
    · exact (gauge_continuousAt hb hρ hp).continuousWithinAt
  · intro r hr
    exact (mul_pos hc (Real.rpow_pos_of_pos hr d)).trans_le
      (le_ciInf (fun i => power_le_entry hd hd2 hc.le (hcb i) (hρ i) hr))

end Envelope

 

theorem finite_exclusions {ι : Type*} [Nonempty ι] (d : ℝ) (b ρ : ι → ℝ)
    (hb : ∀ i, 0 < b i) (hρ : ∀ i, 0 < ρ i) (E : Finset ι)
    (F : ℝ → ℝ) (M C : ℝ)
    (hF : ∀ r, 0 < r → 0 ≤ F r ∧ F r ≤ M)
    (hbound : ∀ i, i ∉ E → ∀ r, 0 < r → F r ≤ C * entry d (b i) (ρ i) r) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ r, 0 < r → F r ≤ C' * gauge d b ρ r := by
  classical
  let A : ι → ℝ := fun i => b i * (ρ i)^d
  have hA (i : ι) : 0 < A i := mul_pos (hb i) (Real.rpow_pos_of_pos (hρ i) d)
  let D : ℝ := max (max 1 C) (∑ i ∈ E, max (M/A i) 0)
  have h1 : 1 ≤ D := (le_max_left 1 C).trans (le_max_left _ _)
  have hD : 0 < D := zero_lt_one.trans_le h1
  have hCD : C ≤ D := (le_max_right 1 C).trans (le_max_left _ _)
  refine ⟨D,hD,?_⟩
  intro r hr
  have hi (i : ι) : F r ≤ D * entry d (b i) (ρ i) r := by
    by_cases hie : i ∈ E
    · have hm : M/A i ≤ D := calc
        M/A i ≤ max (M/A i) 0 := le_max_left _ _
        _ ≤ ∑ j ∈ E, max (M/A j) 0 :=
          Finset.single_le_sum (f := fun j => max (M/A j) 0) (fun j _ => le_max_right _ _) hie
        _ ≤ D := le_max_right _ _
      calc
        F r ≤ M := (hF r hr).2
        _ ≤ D * A i := (div_le_iff₀ (hA i)).mp hm
        _ ≤ D * entry d (b i) (ρ i) r :=
          mul_le_mul_of_nonneg_left (base_le_entry (hb i).le (hρ i)) hD.le
    · exact (hbound i hie r hr).trans
        (mul_le_mul_of_nonneg_right hCD (entry_nonneg (hb i).le (hρ i)))
  rw [mul_comm D]
  apply (div_le_iff₀ hD).mp
  apply le_ciInf
  intro i
  exact (div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hi i)

end SLEExactGauge.QuadraticGauge
end
end

end OAI
