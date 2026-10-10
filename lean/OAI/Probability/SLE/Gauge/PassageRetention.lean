import OAI.Probability.SLE.Geometry.CountableInteriorIntervals
import OAI.Probability.SLE.Geometry.ActualStoppedTubeSupport
import OAI.Probability.SLE.Geometry.FirstHeightBounded

namespace OAI

/-! Countable, measurable retention of actual middle visits and continuation
prefixes. The middle interval is produced from a continuous progress crossing;
the compact certificates are then extracted from fixed countable exhaustions. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace SLEExactGauge.PassageRetention

/-- First crossing of a scalar progress level on a compact time interval. -/
theorem first_progress_crossing
    (x : ℝ → ℝ) {a b q : ℝ} (hab : a < b)
    (hx : ContinuousOn x (Icc a b)) (ha : x a < q) (hb : q < x b) :
    ∃ θ ∈ Ioo a b, x θ = q ∧ ∀ u ∈ Ico a θ, x u < q := by
  let K := Icc a b ∩ x ⁻¹' {q}
  have hKc : IsClosed K := hx.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset hKc inter_subset_left
  have hKn : K.Nonempty := by
    obtain ⟨t, ht, he⟩ := intermediate_value_Icc hab.le hx ⟨ha.le, hb.le⟩
    exact ⟨t, ht, he⟩
  obtain ⟨θ, hθ, hmin⟩ := hK.exists_isLeast hKn
  have he : x θ = q := hθ.2
  have haθ : a < θ := lt_of_le_of_ne hθ.1.1 (by
    intro h
    exact (ne_of_lt ha) (h ▸ he))
  have hθb : θ < b := lt_of_le_of_ne hθ.1.2 (by
    intro h
    exact (ne_of_gt hb) (h ▸ he))
  refine ⟨θ, ⟨haθ, hθb⟩, he, ?_⟩
  intro u hu
  by_contra hn
  obtain ⟨v, hv, hvx⟩ := intermediate_value_Icc hu.1
    (hx.mono (Icc_subset_Icc_right (hu.2.le.trans hθ.1.2))) ⟨ha.le, le_of_not_gt hn⟩
  have hvK : v ∈ K := ⟨⟨hv.1, hv.2.trans (hu.2.le.trans hθ.1.2)⟩, hvx⟩
  exact (not_le_of_gt hu.2) ((hmin hvK).trans hv.2)

def middleRegion (O : Set ℂ) (progress : ℂ → ℝ) : Set ℂ :=
  O ∩ progress ⁻¹' Ioo (1 / 3 : ℝ) (2 / 3)

def beforeFrontRegion (O : Set ℂ) (progress : ℂ → ℝ) : Set ℂ :=
  O ∩ progress ⁻¹' Iio (2 / 3 : ℝ)

def beyondFrontRegion (O : Set ℂ) (progress : ℂ → ℝ) : Set ℂ :=
  O ∩ progress ⁻¹' Ioi (1 : ℝ)

/-- Progress from below one third to beyond the front at one forces a rational
middle interval before the first front crossing and a later rational endpoint. -/
theorem rational_middle_before_front
    (f : ℝ → ℂ) (hf : Continuous f) (O : Set ℂ) (hO : IsOpen O)
    (progress : ℂ → ℝ) (hp : ContinuousOn progress O)
    {a b : ℝ} (hab : a < b) (hfO : MapsTo f (Icc a b) O)
    (hstart : progress (f a) < 1 / 3) (hend : 1 < progress (f b)) :
    ∃ s t u : ℚ, a < (s : ℝ) ∧ (s : ℝ) < t ∧ (t : ℝ) < u ∧ (u : ℝ) < b ∧
      MapsTo f (Icc (s : ℝ) t) (middleRegion O progress) ∧
      MapsTo f (Icc a t) (beforeFrontRegion O progress) ∧
      f u ∈ beyondFrontRegion O progress := by
  let x := progress ∘ f
  have hx : ContinuousOn x (Icc a b) := hp.comp hf.continuousOn hfO
  obtain ⟨θ, hθ, hxθ, hprior⟩ := first_progress_crossing x hab hx
    (show x a < 2 / 3 by dsimp [x]; linarith) (by dsimp [x]; linarith)
  obtain ⟨v, hv, hxv⟩ := intermediate_value_Icc hθ.1.le
    (hx.mono (Icc_subset_Icc_right hθ.2.le))
    (show (1 / 2 : ℝ) ∈ Icc (x a) (x θ) by dsimp [x] at *; rw [hxθ]; constructor <;> linarith)
  have hav : a < v := lt_of_le_of_ne hv.1 (by
    intro he
    subst v
    dsimp [x] at hxv
    linarith)
  have hvθ : v < θ := lt_of_le_of_ne hv.2 (by
    intro he
    subst v
    rw [hxθ] at hxv
    norm_num at hxv)
  have hM : IsOpen (middleRegion O progress) := hp.isOpen_inter_preimage hO isOpen_Ioo
  have hvM : f v ∈ middleRegion O progress :=
    ⟨hfO ⟨hav.le, hvθ.le.trans hθ.2.le⟩, by change (1 / 3 : ℝ) < x v ∧ x v < 2 / 3; rw [hxv]; norm_num⟩
  obtain ⟨s, t, has, hst, htθ, hmid⟩ :=
    exists_rational_interval_in_open_visit f hf _ hM a θ ⟨v, ⟨hav, hvθ⟩, hvM⟩
  have hθb : θ < b := hθ.2
  let q := ((1 : ℝ) + x b) / 2
  have hq : 1 < q ∧ q < x b := by dsimp [q, x]; constructor <;> linarith
  obtain ⟨w, hw, hxw⟩ := intermediate_value_Icc hθb.le
    (hx.mono (Icc_subset_Icc_left hθ.1.le))
    (show q ∈ Icc (x θ) (x b) by rw [hxθ]; exact ⟨by linarith [hq.1], hq.2.le⟩)
  have hθw : θ < w := lt_of_le_of_ne hw.1 (by intro he; subst w; rw [hxθ] at hxw; linarith [hq.1])
  have hwb : w < b := lt_of_le_of_ne hw.2 (by intro he; subst w; linarith [hq.2])
  have hW : IsOpen (beyondFrontRegion O progress) := hp.isOpen_inter_preimage hO isOpen_Ioi
  have hwW : f w ∈ beyondFrontRegion O progress :=
    ⟨hfO ⟨hθ.1.le.trans hw.1, hw.2⟩, by change 1 < x w; rw [hxw]; exact hq.1⟩
  obtain ⟨u, u', hθu, huu', hu'b, hhigh⟩ :=
    exists_rational_interval_in_open_visit f hf _ hW θ b ⟨w, ⟨hθw, hwb⟩, hwW⟩
  refine ⟨s, t, u, has, hst, htθ.trans hθu, huu'.trans hu'b, hmid, ?_, ?_⟩
  · intro v hv
    exact ⟨hfO ⟨hv.1, hv.2.trans (htθ.le.trans hθ.2.le)⟩,
      hprior v ⟨hv.1, hv.2.trans_lt htθ⟩⟩
  · exact hhigh ⟨le_rfl, huu'.le⟩

/-- Fixed compact exhaustions provide countably many certificates for both
the whole continuation and the middle subinterval. -/
theorem exists_compact_passage_certificates
    (O : Set ℂ) (hO : IsOpen O) (progress : ℂ → ℝ)
    (hp : ContinuousOn progress O) :
    ∃ K M L : ℕ → Set ℂ,
      (∀ n, IsCompact (K n) ∧ K n ⊆ O) ∧
      (∀ n, IsCompact (M n) ∧ M n ⊆ middleRegion O progress) ∧
      (∀ n, IsCompact (L n) ∧ L n ⊆ beforeFrontRegion O progress) ∧
      ∀ (f : ℝ → ℂ), Continuous f → ∀ a b : ℝ, a < b →
        MapsTo f (Icc a b) O → progress (f a) < 1 / 3 → 1 < progress (f b) →
        ∃ (s t u : ℚ) (i j k : ℕ),
          a < (s : ℝ) ∧ (s : ℝ) < t ∧ (t : ℝ) < u ∧ (u : ℝ) < b ∧
          f '' Icc a u ⊆ K i ∧ f '' Icc (s : ℝ) t ⊆ M j ∧
          f '' Icc a t ⊆ L k ∧ f u ∈ beyondFrontRegion O progress := by
  obtain ⟨K, hK, hKO, hKcap⟩ := exists_countable_compact_exhaustion_open O hO
  obtain ⟨M, hM, hMO, hMcap⟩ := exists_countable_compact_exhaustion_open
    (middleRegion O progress) (hp.isOpen_inter_preimage hO isOpen_Ioo)
  obtain ⟨L, hL, hLO, hLcap⟩ := exists_countable_compact_exhaustion_open
    (beforeFrontRegion O progress) (hp.isOpen_inter_preimage hO isOpen_Iio)
  refine ⟨K, M, L, fun n => ⟨hK n, hKO n⟩, fun n => ⟨hM n, hMO n⟩,
    fun n => ⟨hL n, hLO n⟩, ?_⟩
  intro f hf a b hab hfO hstart hend
  obtain ⟨s, t, u, has, hst, htu, hub, hmid, hlow, hhigh⟩ :=
    rational_middle_before_front f hf O hO progress hp hab hfO hstart hend
  obtain ⟨i, hi⟩ := hKcap (f '' Icc a u) (isCompact_Icc.image hf)
    ((hfO.mono (Icc_subset_Icc_right hub.le) Subset.rfl).image_subset)
  obtain ⟨j, hj⟩ := hMcap (f '' Icc (s : ℝ) t) (isCompact_Icc.image hf) hmid.image_subset
  obtain ⟨k, hk⟩ := hLcap (f '' Icc a t) (isCompact_Icc.image hf) hlow.image_subset
  exact ⟨s, t, u, i, j, k, has, hst, htu, hub, hi, hj, hk, hhigh⟩

local instance : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

/-- Compact containment from a variable starting time is a closed path test. -/
theorem isClosed_variable_start_compact (u : ℝ≥0) {K : Set ℂ} (hK : IsClosed K) :
    IsClosed {x : ℝ≥0 × C(ℝ≥0, ℂ) | x.1 ≤ u ∧ MapsTo x.2 (Icc x.1 u) K} := by
  have he : {x : ℝ≥0 × C(ℝ≥0, ℂ) | x.1 ≤ u ∧ MapsTo x.2 (Icc x.1 u) K} =
      {x | x.1 ≤ u} ∩ ⋂ t ∈ Icc (0 : ℝ≥0) u, {x | x.2 (max x.1 t) ∈ K} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨hxu, hm⟩
      exact ⟨hxu, fun t ht => hm ⟨le_max_left _ _, max_le hxu ht.2⟩⟩
    · rintro ⟨hxu, hm⟩
      refine ⟨hxu, fun t ht => ?_⟩
      simpa only [max_eq_right ht.1] using hm t ⟨bot_le, ht.2⟩
  rw [he]
  exact (isClosed_le continuous_fst continuous_const).inter
    (isClosed_iInter fun t => isClosed_iInter fun _ =>
      hK.preimage (continuous_eval.comp
        (continuous_snd.prodMk (continuous_fst.max continuous_const))))

theorem measurableSet_variable_start_compact
    {Ω : Type*} [MeasurableSpace Ω] (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (σ : Ω → ℝ≥0) (hσ : Measurable σ) (u : ℝ≥0)
    {K : Set ℂ} (hK : IsCompact K) :
    MeasurableSet {ω | σ ω ≤ u ∧ MapsTo (f ω) (Icc (σ ω) u) K} :=
  (isClosed_variable_start_compact u hK.isClosed).measurableSet.preimage (hσ.prodMk hf)

def ratTime (q : ℚ) : ℝ≥0 := Real.toNNReal (q : ℝ)

@[simp] theorem ratTime_coe {q : ℚ} (hq : 0 ≤ q) : (ratTime q : ℝ) = (q : ℝ) := by
  exact Real.coe_toNNReal _ (by exact_mod_cast hq)

theorem ratTime_lt {p q : ℚ} (hp : 0 ≤ p) (hpq : p < q) : ratTime p < ratTime q := by
  apply NNReal.coe_lt_coe.mp
  rw [ratTime_coe hp, ratTime_coe (hp.trans hpq.le)]
  exact_mod_cast hpq

abbrev RationalPassageTimes := {q : ℚ × ℚ × ℚ // 0 < q.1 ∧ q.1 < q.2.1 ∧ q.2.1 < q.2.2}
abbrev PassageIndex := RationalPassageTimes × (ℕ × ℕ × ℕ)

def intervalStart (i : PassageIndex) : ℝ≥0 := ratTime i.1.1.1
def intervalEnd (i : PassageIndex) : ℝ≥0 := ratTime i.1.1.2.1
def passageEnd (i : PassageIndex) : ℝ≥0 := ratTime i.1.1.2.2

theorem intervalStart_lt_end (i : PassageIndex) : intervalStart i < intervalEnd i :=
  ratTime_lt i.1.2.1.le i.1.2.2.1

theorem intervalEnd_lt_passageEnd (i : PassageIndex) : intervalEnd i < passageEnd i :=
  ratTime_lt (i.1.2.1.le.trans i.1.2.2.1.le) i.1.2.2.2

/-- The three compact tests retain the full prefix, a middle interval, and
a prefix ending before any two-thirds front crossing. -/
def compactPassageCertificate {Ω : Type*} (f : Ω → C(ℝ≥0, ℂ)) (σ : Ω → ℝ≥0)
    (K M L : ℕ → Set ℂ) (W : Set ℂ) (i : PassageIndex) : Set Ω :=
  {ω | σ ω < intervalStart i ∧ f ω (passageEnd i) ∈ W ∧
    (σ ω ≤ passageEnd i ∧ MapsTo (f ω) (Icc (σ ω) (passageEnd i)) (K i.2.1)) ∧
    MapsTo (f ω) (Icc (intervalStart i) (intervalEnd i)) (M i.2.2.1) ∧
    (σ ω ≤ intervalEnd i ∧ MapsTo (f ω) (Icc (σ ω) (intervalEnd i)) (L i.2.2.2))}

theorem compactPassageCertificate_measurable
    {Ω : Type*} [MeasurableSpace Ω] (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (σ : Ω → ℝ≥0) (hσ : Measurable σ)
    (K M L : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n))
    (hM : ∀ n, IsCompact (M n)) (hL : ∀ n, IsCompact (L n))
    (W : Set ℂ) (hW : MeasurableSet W) (i : PassageIndex) :
    MeasurableSet (compactPassageCertificate f σ K M L W i) :=
  (measurableSet_lt hσ measurable_const).inter
    ((hW.preimage ((continuous_eval_const (passageEnd i)).measurable.comp hf)).inter
      ((measurableSet_variable_start_compact f hf σ hσ _ (hK _)).inter
        ((measurableSet_interval_compact_certificate f hf _ _ (hM _)).inter
          (measurableSet_variable_start_compact f hf σ hσ _ (hL _)))))

/-- Fixed compact containment supplies an actual positive open margin. -/
theorem retained_compact_open_margin {K O : Set ℂ} (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ δ : ℝ, 0 < δ ∧ cthickening δ K ⊆ O :=
  hK.exists_cthickening_subset_open hO hKO

/-- A continuous nonnegative-time path with an actual progress crossing
belongs to one of the fixed countable compact certificates. -/
theorem countable_measurable_passage_cover
    {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f) (σ : Ω → ℝ≥0) (hσ : Measurable σ)
    (O : Set ℂ) (hO : IsOpen O) (hOH : O ⊆ upperHalfPlane)
    (progress : ℂ → ℝ) (hp : ContinuousOn progress O) (E : Set Ω)
    (hpass : ∀ ω ∈ E, ∃ b : ℝ≥0, σ ω < b ∧ MapsTo (f ω) (Icc (σ ω) b) O ∧
      progress (f ω (σ ω)) < 1 / 3 ∧ 1 < progress (f ω b)) :
    ∃ K M L : ℕ → Set ℂ,
      (∀ n, IsCompact (K n) ∧ K n ⊆ O) ∧
      (∀ n, IsCompact (M n) ∧ M n ⊆ middleRegion O progress) ∧
      (∀ n, IsCompact (L n) ∧ L n ⊆ beforeFrontRegion O progress) ∧
      (∀ n, K n ⊆ upperHalfPlane) ∧ (∀ n, M n ⊆ upperHalfPlane) ∧
      (∀ i, MeasurableSet (compactPassageCertificate f σ K M L
        (beyondFrontRegion O progress) i)) ∧
      E ⊆ ⋃ i : PassageIndex, compactPassageCertificate f σ K M L
        (beyondFrontRegion O progress) i := by
  obtain ⟨K, M, L, hK, hM, hL, hcert⟩ := exists_compact_passage_certificates O hO progress hp
  refine ⟨K, M, L, hK, hM, hL, fun n => (hK n).2.trans hOH,
    fun n z hz => hOH ((hM n).2 hz).1, ?_, ?_⟩
  · exact fun i => compactPassageCertificate_measurable f hf σ hσ K M L
      (fun n => (hK n).1) (fun n => (hM n).1) (fun n => (hL n).1)
      _ (hp.isOpen_inter_preimage hO isOpen_Ioi).measurableSet i
  · intro ω hω
    obtain ⟨b, hσb, hfO, hstart, hend⟩ := hpass ω hω
    let fR : ℝ → ℂ := fun t => f ω (Real.toNNReal t)
    have hfR : Continuous fR := (f ω).continuous.comp continuous_real_toNNReal
    have hfRO : MapsTo fR (Icc (σ ω : ℝ) (b : ℝ)) O := by
      intro t ht
      have ht0 : 0 ≤ t := (σ ω).coe_nonneg.trans ht.1
      apply hfO
      constructor
      · apply NNReal.coe_le_coe.mp
        simpa only [Real.coe_toNNReal _ ht0] using ht.1
      · apply NNReal.coe_le_coe.mp
        simpa only [Real.coe_toNNReal _ ht0] using ht.2
    obtain ⟨s, t, u, i, j, k, has, hst, htu, hub, hpre, hmid, hlow, hhigh⟩ :=
      hcert fR hfR (σ ω) b hσb hfRO
        (by simpa only [fR, Real.toNNReal_coe] using hstart)
        (by simpa only [fR, Real.toNNReal_coe] using hend)
    have hs : 0 < s := by exact_mod_cast ((σ ω).coe_nonneg.trans_lt has)
    have hst' : s < t := by exact_mod_cast hst
    have htu' : t < u := by exact_mod_cast htu
    have ht : 0 ≤ t := hs.le.trans hst'.le
    have hu : 0 ≤ u := ht.trans htu'.le
    let idx : PassageIndex := ⟨⟨(s, t, u), hs, hst', htu'⟩, (i, j, k)⟩
    apply mem_iUnion.mpr
    refine ⟨idx, ?_⟩
    change σ ω < ratTime s ∧ f ω (ratTime u) ∈ beyondFrontRegion O progress ∧
      (σ ω ≤ ratTime u ∧ MapsTo (f ω) (Icc (σ ω) (ratTime u)) (K i)) ∧
      MapsTo (f ω) (Icc (ratTime s) (ratTime t)) (M j) ∧
      (σ ω ≤ ratTime t ∧ MapsTo (f ω) (Icc (σ ω) (ratTime t)) (L k))
    have has' : σ ω < ratTime s := by
      apply NNReal.coe_lt_coe.mp
      simpa only [ratTime_coe hs.le] using has
    have lift (a : ℝ≥0) (q : ℚ) (hq : 0 ≤ q) (A : Set ℂ)
        (hA : fR '' Icc (a : ℝ) (q : ℝ) ⊆ A) : MapsTo (f ω) (Icc a (ratTime q)) A := by
      intro v hv
      apply hA
      refine ⟨(v : ℝ), ?_, ?_⟩
      · constructor
        · exact_mod_cast hv.1
        · have hh : (v : ℝ) ≤ (ratTime q : ℝ) := hv.2
          simpa only [ratTime_coe hq] using hh
      · simp only [fR, Real.toNNReal_coe]
    refine ⟨has', hhigh, ⟨has'.le.trans ((ratTime_lt hs.le hst').le.trans
      (ratTime_lt ht htu').le), lift _ _ hu _ hpre⟩, ?_,
      ⟨has'.le.trans (ratTime_lt hs.le hst').le, lift _ _ ht _ hlow⟩⟩
    apply lift _ _ ht
    simpa only [ratTime_coe hs.le] using hmid

/-- The actual future tube event supplies the progress-crossing hypothesis;
no compact or interval certificate is assumed. -/
theorem stopped_tube_has_countable_passage_cover
    {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f) (σ : Ω → ℝ≥0) (hσ : Measurable σ)
    (O W : Set ℂ) (hO : IsOpen O) (hOH : O ⊆ upperHalfPlane)
    (progress : ℂ → ℝ) (hp : ContinuousOn progress O)
    (hW : W ⊆ {z | 1 < progress z}) (E : Set Ω)
    (hE : E ⊆ stoppedPhysicalTube (fun ω => f ω) σ O W)
    (hstart : ∀ ω ∈ E, progress (f ω (σ ω)) < 1 / 3) :
    ∃ K M L : ℕ → Set ℂ,
      (∀ n, IsCompact (K n) ∧ K n ⊆ O) ∧
      (∀ n, IsCompact (M n) ∧ M n ⊆ middleRegion O progress) ∧
      (∀ n, IsCompact (L n) ∧ L n ⊆ beforeFrontRegion O progress) ∧
      (∀ n, K n ⊆ upperHalfPlane) ∧ (∀ n, M n ⊆ upperHalfPlane) ∧
      (∀ i, MeasurableSet (compactPassageCertificate f σ K M L
        (beyondFrontRegion O progress) i)) ∧
      E ⊆ ⋃ i : PassageIndex, compactPassageCertificate f σ K M L
        (beyondFrontRegion O progress) i := by
  apply countable_measurable_passage_cover f hf σ hσ O hO hOH progress hp E
  intro ω hω
  obtain ⟨T, hT, hpath, hend⟩ := hE hω
  refine ⟨σ ω + T, lt_add_of_pos_right _ hT, ?_, hstart ω hω, hW hend⟩
  intro t ht
  have hdiff : t - σ ω ∈ Icc (0 : ℝ≥0) T := by
    exact ⟨bot_le, tsub_le_iff_right.mpr (by simpa only [add_comm] using ht.2)⟩
  simpa only [add_tsub_cancel_of_le ht.1] using hpath hdiff

abbrev RetainedPassageIndex := PassageIndex × ℕ

def retainedPassageCertificate {Ω : Type*} (f : Ω → C(ℝ≥0, ℂ)) (σ : Ω → ℝ≥0)
    (K M L N : ℕ → Set ℂ) (W : Set ℂ) (i : RetainedPassageIndex) : Set Ω :=
  compactPassageCertificate f σ K M L W i.1 ∩
    {ω | f ω (passageEnd i.1) ∈ N i.2}

/-- Actual tube passages admit a countable measurable cover with compact
endpoint margins as well as compact prefix and middle margins. -/
theorem stopped_tube_retained_cover
    {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f) (σ : Ω → ℝ≥0) (hσ : Measurable σ)
    (O W : Set ℂ) (hO : IsOpen O) (hOH : O ⊆ upperHalfPlane)
    (progress : ℂ → ℝ) (hp : ContinuousOn progress O)
    (hW : W ⊆ {z | 1 < progress z}) (E : Set Ω)
    (hE : E ⊆ stoppedPhysicalTube (fun ω => f ω) σ O W)
    (hstart : ∀ ω ∈ E, progress (f ω (σ ω)) < 1 / 3) :
    ∃ K M L N : ℕ → Set ℂ,
      (∀ n, IsCompact (K n) ∧ K n ⊆ O) ∧
      (∀ n, IsCompact (M n) ∧ M n ⊆ middleRegion O progress) ∧
      (∀ n, IsCompact (L n) ∧ L n ⊆ beforeFrontRegion O progress) ∧
      (∀ n, IsCompact (N n) ∧ N n ⊆ beyondFrontRegion O progress) ∧
      (∀ i, MeasurableSet (retainedPassageCertificate f σ K M L N
        (beyondFrontRegion O progress) i)) ∧
      E ⊆ ⋃ i : RetainedPassageIndex, retainedPassageCertificate f σ K M L N
        (beyondFrontRegion O progress) i := by
  obtain ⟨K, M, L, hK, hM, hL, _, _, hDm, hcover⟩ :=
    stopped_tube_has_countable_passage_cover f hf σ hσ O W hO hOH progress hp hW E hE hstart
  obtain ⟨N, hN, hNO, hNcap⟩ := exists_countable_compact_exhaustion_open
    (beyondFrontRegion O progress) (hp.isOpen_inter_preimage hO isOpen_Ioi)
  refine ⟨K, M, L, N, hK, hM, hL, fun n => ⟨hN n, hNO n⟩, ?_, ?_⟩
  · intro i
    exact (hDm i.1).inter ((hN i.2).measurableSet.preimage
      ((continuous_eval_const (passageEnd i.1)).measurable.comp hf))
  · intro ω hω
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hω)
    have hend : f ω (passageEnd i) ∈ beyondFrontRegion O progress := hi.2.1
    obtain ⟨j, hj⟩ := hNcap {f ω (passageEnd i)} isCompact_singleton
      (singleton_subset_iff.mpr hend)
    exact mem_iUnion.mpr ⟨(i, j), hi, hj (mem_singleton _)⟩

/-- On each retained certificate all strict passage conditions transfer
uniformly to sufficiently late locally convergent maps. -/
theorem retained_certificate_transfers
    {Ω : Type*} (f : Ω → C(ℝ≥0, ℂ)) (σ : Ω → ℝ≥0)
    (K M L N : ℕ → Set ℂ) (W : Set ℂ) (i : RetainedPassageIndex)
    (Fₙ : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hconv : TendstoLocallyUniformlyOn Fₙ F atTop upperHalfPlane)
    (hF : ContinuousOn F upperHalfPlane)
    (hK : IsCompact (K i.1.2.1)) (hKH : K i.1.2.1 ⊆ upperHalfPlane)
    (hM : IsCompact (M i.1.2.2.1)) (hMH : M i.1.2.2.1 ⊆ upperHalfPlane)
    (hL : IsCompact (L i.1.2.2.2)) (hLH : L i.1.2.2.2 ⊆ upperHalfPlane)
    (hN : IsCompact (N i.2)) (hNH : N i.2 ⊆ upperHalfPlane)
    (R Rmid Rlow Rhigh : Set ℂ)
    (hR : IsOpen R) (hRmid : IsOpen Rmid) (hRlow : IsOpen Rlow) (hRhigh : IsOpen Rhigh)
    (hKR : F '' K i.1.2.1 ⊆ R) (hMR : F '' M i.1.2.2.1 ⊆ Rmid)
    (hLR : F '' L i.1.2.2.2 ⊆ Rlow) (hNR : F '' N i.2 ⊆ Rhigh) :
    ∀ᶠ n in atTop, ∀ ω ∈ retainedPassageCertificate f σ K M L N W i,
      MapsTo (fun t => Fₙ n (f ω t)) (Icc (σ ω) (passageEnd i.1)) R ∧
      MapsTo (fun t => Fₙ n (f ω t)) (Icc (intervalStart i.1) (intervalEnd i.1)) Rmid ∧
      MapsTo (fun t => Fₙ n (f ω t)) (Icc (σ ω) (intervalEnd i.1)) Rlow ∧
      Fₙ n (f ω (passageEnd i.1)) ∈ Rhigh := by
  filter_upwards [eventually_image_compact_subset_open Fₙ F hconv hF _ hK hKH R hR hKR,
    eventually_image_compact_subset_open Fₙ F hconv hF _ hM hMH Rmid hRmid hMR,
    eventually_image_compact_subset_open Fₙ F hconv hF _ hL hLH Rlow hRlow hLR,
    eventually_image_compact_subset_open Fₙ F hconv hF _ hN hNH Rhigh hRhigh hNR]
    with n hnK hnM hnL hnN
  rintro ω ⟨⟨_, _, hpre, hmid, hlow⟩, hend⟩
  exact ⟨fun t ht => hnK (mem_image_of_mem _ (hpre.2 ht)),
    fun t ht => hnM (mem_image_of_mem _ (hmid ht)),
    fun t ht => hnL (mem_image_of_mem _ (hlow.2 ht)), hnN (mem_image_of_mem _ hend)⟩

/-- The middle interval lies before every later time which attains the
front level; in particular it precedes the first such passage stop. -/
theorem retained_interval_before_front
    {Ω : Type*} (f : Ω → C(ℝ≥0, ℂ)) (σ : Ω → ℝ≥0)
    (K M L N : ℕ → Set ℂ) (W : Set ℂ) (i : RetainedPassageIndex)
    (progress : ℂ → ℝ) (hL : ∀ z ∈ L i.1.2.2.2, progress z < 2 / 3)
    (ω : Ω) (hω : ω ∈ retainedPassageCertificate f σ K M L N W i)
    (τ : ℝ≥0) (hστ : σ ω ≤ τ) (hτ : 2 / 3 ≤ progress (f ω τ)) :
    intervalEnd i.1 < τ := by
  by_contra hn
  have hlow := hω.1.2.2.2.2.2
  have hh := hL _ (hlow ⟨hστ, le_of_not_gt hn⟩)
  exact (not_le_of_gt hh) hτ

instance rationalPassageTimes_nonempty : Nonempty RationalPassageTimes :=
  ⟨⟨(1, 2, 3), by norm_num⟩⟩

/-- Enumerating the concrete rational/compact indices gives the natural
indexing expected by finite-retention and unconditional sausage lemmas. -/
def enumerateRetainedPassage : ℕ → RetainedPassageIndex :=
  (exists_surjective_nat RetainedPassageIndex).choose

theorem enumerateRetainedPassage_surjective : Function.Surjective enumerateRetainedPassage :=
  (exists_surjective_nat RetainedPassageIndex).choose_spec

theorem nat_retained_cover
    {Ω : Type*} (f : Ω → C(ℝ≥0, ℂ)) (σ : Ω → ℝ≥0)
    (K M L N : ℕ → Set ℂ) (W : Set ℂ) (E : Set Ω)
    (hcover : E ⊆ ⋃ i : RetainedPassageIndex, retainedPassageCertificate f σ K M L N W i) :
    E ⊆ ⋃ n : ℕ, retainedPassageCertificate f σ K M L N W (enumerateRetainedPassage n) := by
  intro ω hω
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hω)
  obtain ⟨n, rfl⟩ := enumerateRetainedPassage_surjective i
  exact mem_iUnion.mpr ⟨n, hi⟩

end SLEExactGauge.PassageRetention

end

end OAI
