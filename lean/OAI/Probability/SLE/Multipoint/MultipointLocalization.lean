import OAI.Probability.SLE.FiniteRadiusStop
import OAI.Probability.SLE.Multipoint.MultipointStoppedCoordinates

namespace OAI

/-! A finite localization for the completion-frozen logarithmic coordinates.
Only the log heights and the real driver are cut off; the smooth factors
need no angular cutoff. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

def localizationMarginTerm {ι : Type*} (lo hi M : ℝ)
    (q : ι → ℂ × ℝ) (b : ℝ) : Option ι → ℝ
  | none => M-|b|
  | some i => min ((q i).1.im-lo) (hi-(q i).1.im)

/-- The extra `none` index is the driver margin, so empty point families
are allowed without an artificial height condition. -/
def localizationMargin {ι : Type*} [Fintype ι] (lo hi M : ℝ)
    (q : ι → ℂ × ℝ) (b : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (localizationMarginTerm lo hi M q b)

lemma localizationMargin_nonneg_iff {ι : Type*} [Fintype ι]
    (lo hi M : ℝ) (q : ι → ℂ × ℝ) (b : ℝ) :
    0 ≤ localizationMargin lo hi M q b ↔
      (∀ i, lo ≤ (q i).1.im ∧ (q i).1.im ≤ hi) ∧ |b| ≤ M := by
  classical
  rw [localizationMargin, Finset.le_inf'_iff]
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have hi := h (some i) (Finset.mem_univ _)
      simpa only [localizationMarginTerm, le_min_iff, sub_nonneg] using hi
    · exact sub_nonneg.mp (h none (Finset.mem_univ _))
  · rintro ⟨hq,hb⟩ i _
    cases i with
    | none => exact sub_nonneg.mpr hb
    | some i =>
      exact le_min (sub_nonneg.mpr (hq i).1) (sub_nonneg.mpr (hq i).2)

lemma localizationMargin_pos_iff {ι : Type*} [Fintype ι]
    (lo hi M : ℝ) (q : ι → ℂ × ℝ) (b : ℝ) :
    0 < localizationMargin lo hi M q b ↔
      (∀ i, lo < (q i).1.im ∧ (q i).1.im < hi) ∧ |b| < M := by
  classical
  rw [localizationMargin, Finset.lt_inf'_iff]
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have hi := h (some i) (Finset.mem_univ _)
      simpa only [localizationMarginTerm, lt_min_iff, sub_pos] using hi
    · exact sub_pos.mp (h none (Finset.mem_univ _))
  · rintro ⟨hq,hb⟩ i _
    cases i with
    | none => exact sub_pos.mpr hb
    | some i =>
      exact lt_min (sub_pos.mpr (hq i).1) (sub_pos.mpr (hq i).2)

lemma localizationMargin_continuous {ι : Type*} [Fintype ι]
    (lo hi M : ℝ) :
    Continuous (fun p : (ι → ℂ × ℝ) × ℝ => localizationMargin lo hi M p.1 p.2) := by
  classical
  unfold localizationMargin
  apply Continuous.finset_inf'_apply
  intro i _
  cases i with
  | none => exact continuous_const.sub continuous_snd.abs
  | some i =>
    have hc : Continuous (fun p : (ι → ℂ × ℝ) × ℝ => (p.1 i).1.im) :=
      Complex.continuous_im.comp (((continuous_apply i).comp continuous_fst).fst)
    exact (hc.sub continuous_const).min (continuous_const.sub hc)

lemma localizationMargin_boundary {ι : Type*} [Fintype ι]
    (lo hi M : ℝ) (q : ι → ℂ × ℝ) (b : ℝ)
    (hn : 0 ≤ localizationMargin lo hi M q b)
    (hz : localizationMargin lo hi M q b = 0) :
    (∃ i, (q i).1.im = lo ∨ (q i).1.im = hi) ∨ |b| = M := by
  classical
  obtain ⟨hq,hb⟩ := (localizationMargin_nonneg_iff lo hi M q b).mp hn
  have hzle : localizationMargin lo hi M q b ≤ 0 := hz.le
  rw [localizationMargin, Finset.inf'_le_iff] at hzle
  obtain ⟨i, _, hterm⟩ := hzle
  cases i with
  | none =>
    right
    change M-|b| ≤ 0 at hterm
    linarith
  | some i =>
    left
    refine ⟨i, ?_⟩
    change min ((q i).1.im-lo) (hi-(q i).1.im) ≤ 0 at hterm
    rcases min_le_iff.mp hterm with hl | hh
    · left
      linarith [(hq i).1]
    · right
      linarith [(hq i).2]

/-- Stop the continuous adapted state at the first height or driver
boundary, capped at the deterministic horizon. -/
theorem exists_multipoint_localization
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    (ℱ : Filtration ℝ≥0 mΩ)
    (Q : ℝ → Ω → ι → ℂ × ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hQa : Adapted ℱ (fun t : ℝ≥0 => Q t))
    (hQc : ∀ ω, Continuous (fun t : ℝ => Q t ω))
    (hBa : Adapted ℱ B) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (lo hi M : ℝ) (H : ℝ≥0)
    (hQ0 : ∀ ω i, lo ≤ (Q 0 ω i).1.im ∧ (Q 0 ω i).1.im ≤ hi)
    (hB0 : ∀ ω, |B 0 ω| ≤ M) :
    ∃ χ : Ω → ℝ≥0,
      IsStoppingTime ℱ (fun ω => (χ ω : WithTop ℝ≥0)) ∧
      (∀ ω, χ ω ≤ H) ∧
      (∀ ω t, t ≤ χ ω →
        (∀ i, lo ≤ (Q t ω i).1.im ∧ (Q t ω i).1.im ≤ hi) ∧ |B t ω| ≤ M) ∧
      (∀ ω t, t < χ ω →
        (∀ i, lo < (Q t ω i).1.im ∧ (Q t ω i).1.im < hi) ∧ |B t ω| < M) ∧
      (∀ ω, χ ω < H →
        (∃ i, (Q (χ ω) ω i).1.im = lo ∨ (Q (χ ω) ω i).1.im = hi) ∨
          |B (χ ω) ω| = M) := by
  let D := fun (t : ℝ≥0) ω => localizationMargin lo hi M (Q t ω) (B t ω)
  have hmc : Continuous (fun p : (ι → ℂ × ℝ) × ℝ =>
      localizationMargin lo hi M p.1 p.2) :=
    localizationMargin_continuous (ι := ι) lo hi M
  have hDa : Adapted ℱ D := by
    intro t
    change Measurable[ℱ t] ((fun p : (ι → ℂ × ℝ) × ℝ =>
      localizationMargin lo hi M p.1 p.2) ∘ (fun ω => (Q t ω,B t ω)))
    exact hmc.measurable.comp ((hQa t).prodMk (hBa t))
  have hDc (ω : Ω) : Continuous (fun t => D t ω) :=
    hmc.comp
      (((hQc ω).comp NNReal.continuous_coe).prodMk (hBc ω))
  have hD0 (ω : Ω) : 0 ≤ D 0 ω :=
    (localizationMargin_nonneg_iff lo hi M (Q 0 ω) (B 0 ω)).mpr ⟨hQ0 ω,hB0 ω⟩
  obtain ⟨χ,hχ,hH,hn,hp,hz⟩ := first_margin_stopping ℱ D hDa hDc hD0 H
  refine ⟨χ,hχ,hH,?_,?_,?_⟩
  · intro ω t ht
    exact (localizationMargin_nonneg_iff lo hi M (Q t ω) (B t ω)).mp (hn ω t ht)
  · intro ω t ht
    exact (localizationMargin_pos_iff lo hi M (Q t ω) (B t ω)).mp (hp ω t ht)
  · intro ω ht
    exact localizationMargin_boundary lo hi M (Q (χ ω) ω) (B (χ ω) ω)
      (hn ω (χ ω) le_rfl) (hz ω ht)

end SLEExactGauge.Multipoint

end

end OAI
