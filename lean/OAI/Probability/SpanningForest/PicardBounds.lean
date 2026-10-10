import Mathlib

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped Topology NNReal

namespace Problem336.DeterministicDecoder

def picardBound (L T : ℝ) (n : ℕ) : ℝ :=
  L ^ n * T ^ (n + 1) / (n + 1).factorial

lemma picardBound_nonneg {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) (n : ℕ) :
    0 ≤ picardBound L T n := by
  unfold picardBound
  positivity

lemma picardBound_le_exp_term {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) (n : ℕ) :
    picardBound L T n ≤ T * ((L * T) ^ n / n.factorial) := by
  have hfac : (n.factorial : ℝ) ≤ ((n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  calc
    picardBound L T n = T * (L * T) ^ n / (n + 1).factorial := by
      simp only [picardBound, mul_pow, pow_succ]
      ring
    _ ≤ T * (L * T) ^ n / n.factorial := by
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · exact hfac
    _ = T * ((L * T) ^ n / n.factorial) := by ring

lemma summable_picardBound {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) :
    Summable (picardBound L T) := by
  exact Summable.of_nonneg_of_le (picardBound_nonneg hL hT)
    (picardBound_le_exp_term hL hT)
    ((Real.summable_pow_div_factorial (L * T)).mul_left T)

lemma tendsto_picardBound_zero {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) :
    Tendsto (picardBound L T) atTop (𝓝 0) :=
  (summable_picardBound hL hT).tendsto_atTop_zero

theorem exists_uniform_limit_of_summable_increments
    {ι E : Type*} [MetricSpace E] [CompleteSpace E]
    (z : ℕ → ι → E) (d : ℕ → ℝ) (hd : Summable d)
    (hz : ∀ n i, dist (z n i) (z (n + 1) i) ≤ d n) :
    ∃ limit : ι → E, TendstoUniformly z limit atTop ∧
      ∀ n i, dist (z n i) (limit i) ≤ ∑' k, d (n + k) := by
  have hc : ∀ i, CauchySeq (fun n => z n i) := fun i =>
    cauchySeq_of_dist_le_of_summable d (fun n => hz n i) hd
  choose limit hlimit using fun i => cauchySeq_tendsto_of_complete (hc i)
  have hbound : ∀ n i, dist (z n i) (limit i) ≤ ∑' k, d (n + k) := by
    intro n i
    exact dist_le_tsum_of_dist_le_of_tendsto d (fun k => hz k i) hd (hlimit i) n
  refine ⟨limit, ?_, hbound⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have htail : Tendsto (fun n => ∑' k, d (n + k)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using tendsto_sum_nat_add d
  filter_upwards [(tendsto_order.mp htail).2 ε hε] with n hn
  intro i
  rw [dist_comm]
  exact (hbound n i).trans_lt hn

theorem exists_uniform_limit_of_picard_increments
    {ι E : Type*} [MetricSpace E] [CompleteSpace E]
    (z : ℕ → ι → E) {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hz : ∀ n i, dist (z n i) (z (n + 1) i) ≤ picardBound L T n) :
    ∃ limit : ι → E, TendstoUniformly z limit atTop ∧
      ∀ n i, dist (z n i) (limit i) ≤ ∑' k, picardBound L T (n + k) :=
  exists_uniform_limit_of_summable_increments z (picardBound L T)
    (summable_picardBound hL hT) hz

theorem unique_of_picard_approximation
    {ι E : Type*} [MetricSpace E] (z : ℕ → ι → E) (x y : ι → E)
    {L T : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hx : ∀ n i, dist (x i) (z n i) ≤ picardBound L T n)
    (hy : ∀ n i, dist (y i) (z n i) ≤ picardBound L T n) : x = y := by
  funext i
  apply dist_eq_zero.mp
  apply le_antisymm _ dist_nonneg
  have ht : Tendsto (fun n => 2 * picardBound L T n) atTop (𝓝 0) := by
    simpa using (tendsto_picardBound_zero hL hT).const_mul 2
  apply ge_of_tendsto' ht
  intro n
  calc
    dist (x i) (y i) ≤ dist (x i) (z n i) + dist (z n i) (y i) := dist_triangle _ _ _
    _ ≤ picardBound L T n + picardBound L T n := by
      rw [dist_comm (z n i) (y i)]
      exact add_le_add (hx n i) (hy n i)
    _ = 2 * picardBound L T n := by ring

theorem uniform_drift_convergence
    {ι τ : Type*} (b : τ → (ι → ℝ) → ι → ℝ)
    {L : ℝ} (hL : 0 ≤ L)
    (hresponse : ∀ t x y D, 0 ≤ D →
      (∀ j, dist (x j) (y j) ≤ D) →
      ∀ i, dist (b t x i) (b t y i) ≤ L * D)
    (z : ℕ → ι → τ → ℝ) (limit : ι → τ → ℝ)
    (hz : TendstoUniformly (fun n (p : ι × τ) => z n p.1 p.2)
      (fun p => limit p.1 p.2) atTop) :
    TendstoUniformly (fun n (p : ι × τ) => b p.2 (fun j => z n j p.2) p.1)
      (fun p => b p.2 (fun j => limit j p.2) p.1) atTop := by
  rw [Metric.tendstoUniformly_iff] at hz ⊢
  intro ε hε
  have hpos : 0 < L + 1 := by linarith
  have hδ : 0 < ε / (L + 1) := div_pos hε hpos
  filter_upwards [hz (ε / (L + 1)) hδ] with n hn
  intro p
  have hr := hresponse p.2 (fun j => limit j p.2) (fun j => z n j p.2)
    (ε / (L + 1)) hδ.le (fun j => (hn (j, p.2)).le) p.1
  have hid : (L + 1) * (ε / (L + 1)) = ε := by
    field_simp
  exact hr.trans_lt (by nlinarith)

theorem continuous_coordinate_of_uniform_limit
    {ι τ E : Type*} [TopologicalSpace τ] [MetricSpace E]
    (z : ℕ → ι → τ → E) (limit : ι → τ → E)
    (hz : TendstoUniformly (fun n (p : ι × τ) => z n p.1 p.2)
      (fun p => limit p.1 p.2) atTop)
    (hc : ∀ n i, Continuous (z n i)) (i : ι) : Continuous (limit i) := by
  have hi := hz.comp (fun t => (i, t))
  exact hi.continuous (Filter.Eventually.of_forall (fun n => hc n i)).frequently

lemma picardBound_mono_time {L s T : ℝ} (hL : 0 ≤ L) (hs : 0 ≤ s)
    (hsT : s ≤ T) (n : ℕ) : picardBound L s n ≤ picardBound L T n := by
  unfold picardBound
  gcongr

def sequenceLimit {ι : Type*} (z : ℕ → ι → ℝ → ℝ) (i : ι) (t : ℝ) : ℝ :=
  limUnder atTop (fun n => z n i t)

lemma tendsto_sequenceLimit_of_picard_increments
    {ι : Type*} (z : ℕ → ι → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hz : ∀ n i t, 0 ≤ t → dist (z n i t) (z (n + 1) i t) ≤ picardBound L t n)
    (i : ι) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => z n i t) atTop (𝓝 (sequenceLimit z i t)) := by
  apply tendsto_nhds_limUnder
  exact cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable (picardBound L t)
      (fun n => hz n i t ht) (summable_picardBound hL ht))

theorem compact_uniform_sequenceLimit
    {ι : Type*} (z : ℕ → ι → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hz : ∀ n i t, 0 ≤ t → dist (z n i t) (z (n + 1) i t) ≤ picardBound L t n)
    {T : ℝ} (hT : 0 ≤ T) :
    TendstoUniformly
      (fun n (p : ι × Set.Icc (0 : ℝ) T) => z n p.1 p.2)
      (fun p => sequenceLimit z p.1 p.2) atTop ∧
    ∀ n i t, t ∈ Set.Icc (0 : ℝ) T →
      dist (z n i t) (sequenceLimit z i t) ≤ ∑' k, picardBound L T (n + k) := by
  have hinc : ∀ n (p : ι × Set.Icc (0 : ℝ) T),
      dist (z n p.1 p.2) (z (n + 1) p.1 p.2) ≤ picardBound L T n := by
    intro n p
    exact (hz n p.1 p.2 p.2.property.1).trans
      (picardBound_mono_time hL p.2.property.1 p.2.property.2 n)
  obtain ⟨limit, hconv, hbound⟩ := exists_uniform_limit_of_picard_increments
    (fun n (p : ι × Set.Icc (0 : ℝ) T) => z n p.1 p.2) hL hT hinc
  have heq : limit = fun p => sequenceLimit z p.1 p.2 := by
    funext p
    exact tendsto_nhds_unique (hconv.tendsto_at p)
      (tendsto_sequenceLimit_of_picard_increments z hL hz p.1 p.2.property.1)
  subst limit
  refine ⟨hconv, ?_⟩
  intro n i t ht
  exact hbound n (i, ⟨t, ht⟩)

theorem continuousOn_sequenceLimit
    {ι : Type*} (z : ℕ → ι → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hz : ∀ n i t, 0 ≤ t → dist (z n i t) (z (n + 1) i t) ≤ picardBound L t n)
    (hc : ∀ n i, Continuous (z n i)) (i : ι) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (sequenceLimit z i) (Set.Icc (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_coordinate_of_uniform_limit
    (fun n i (s : Set.Icc (0 : ℝ) T) => z n i s)
    (fun i (s : Set.Icc (0 : ℝ) T) => sequenceLimit z i s)
    (compact_uniform_sequenceLimit z hL hz hT).1
    (fun n i => (hc n i).comp continuous_subtype_val) i

theorem continuousOn_sequenceLimit_nonnegative
    {ι : Type*} (z : ℕ → ι → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hz : ∀ n i t, 0 ≤ t → dist (z n i t) (z (n + 1) i t) ≤ picardBound L t n)
    (hc : ∀ n i, Continuous (z n i)) (i : ι) :
    ContinuousOn (sequenceLimit z i) (Set.Ici (0 : ℝ)) := by
  apply continuousOn_of_locally_continuousOn
  intro t ht
  refine ⟨Set.Iio (t + 1), isOpen_Iio, by simp, ?_⟩
  have hT : 0 ≤ t + 1 := by have := ht; simp only [Set.mem_Ici] at this; linarith
  apply (continuousOn_sequenceLimit z hL hz hc i hT).mono
  intro s hs
  exact ⟨hs.1, hs.2.le⟩

theorem continuous_sequenceLimit_nnreal
    {ι : Type*} (z : ℕ → ι → ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hz : ∀ n i t, 0 ≤ t → dist (z n i t) (z (n + 1) i t) ≤ picardBound L t n)
    (hc : ∀ n i, Continuous (z n i)) (i : ι) :
    Continuous (fun t : ℝ≥0 => sequenceLimit z i t) := by
  exact (continuousOn_iff_continuous_domRestrict.mp
    (continuousOn_sequenceLimit_nonnegative z hL hz hc i))

theorem integral_equation_at_of_uniform_limit
    {ι : Type*} (b : ℝ → (ι → ℝ) → ι → ℝ)
    (w : ι → ℝ → ℝ) (z : ℕ → ι → ℝ → ℝ) (limit : ι → ℝ → ℝ)
    {L T M : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hresponse : ∀ t x y D, 0 ≤ D →
      (∀ j, dist (x j) (y j) ≤ D) →
      ∀ i, dist (b t x i) (b t y i) ≤ L * D)
    (hbound : ∀ t x i, |b t x i| ≤ M)
    (hmeas : ∀ n i, Measurable (fun s => b s (fun j => z n j s) i))
    (hz : TendstoUniformly
      (fun n (p : ι × Set.Icc (0 : ℝ) T) => z n p.1 p.2)
      (fun p => limit p.1 p.2) atTop)
    (hrec : ∀ n i, z (n + 1) i T = w i T +
      ∫ s in (0 : ℝ)..T, b s (fun j => z n j s) i) :
    ∀ i, limit i T = w i T + ∫ s in (0 : ℝ)..T, b s (fun j => limit j s) i := by
  have hdb := uniform_drift_convergence
    (fun (s : Set.Icc (0 : ℝ) T) => b s) hL
    (fun s => hresponse s)
    (fun n i (s : Set.Icc (0 : ℝ) T) => z n i s)
    (fun i (s : Set.Icc (0 : ℝ) T) => limit i s) hz
  intro i
  have hint : Tendsto (fun n => ∫ s in (0 : ℝ)..T, b s (fun j => z n j s) i)
      atTop (𝓝 (∫ s in (0 : ℝ)..T, b s (fun j => limit j s) i)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    · exact Eventually.of_forall (fun n => (hmeas n i).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n => Eventually.of_forall (fun s _ => by
        simpa only [Real.norm_eq_abs] using hbound s (fun j => z n j s) i))
    · exact intervalIntegrable_const
    · apply Eventually.of_forall
      intro s hs
      rw [Set.uIoc_of_le hT] at hs
      exact hdb.tendsto_at (i, ⟨s, hs.1.le, hs.2⟩)
  have hpoint : Tendsto (fun n => z n i T) atTop (𝓝 (limit i T)) :=
    hz.tendsto_at (i, ⟨T, hT, le_rfl⟩)
  have hsucc : Tendsto (fun n => z (n + 1) i T) atTop (𝓝 (limit i T)) :=
    hpoint.comp (tendsto_add_atTop_nat 1)
  have heq : Tendsto (fun n => z (n + 1) i T) atTop
      (𝓝 (w i T + ∫ s in (0 : ℝ)..T, b s (fun j => limit j s) i)) := by
    exact (tendsto_const_nhds.add hint).congr' (Eventually.of_forall (fun n => (hrec n i).symm))
  exact tendsto_nhds_unique hsucc heq

end Problem336.DeterministicDecoder

end

end OAI
