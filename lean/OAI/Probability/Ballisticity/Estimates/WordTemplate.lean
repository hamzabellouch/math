import Mathlib
import OAI.Probability.Ballisticity.Geometry.LatticeVector

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma independent_past_current {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (W : ℕ → Ω → β) (hW : ∀ i, Measurable (W i))
    (hInd : iIndepFun W μ) (i : ℕ) :
    IndepFun (fun x => fun j : Fin i => W j x) (W i) μ := by
  have hd : Disjoint (Finset.range i) {i} := by simp
  have hh := hInd.indepFun_finset (Finset.range i) {i} hd hW
  have hc := hh.comp
    (show Measurable (fun f : (j : ↑(Finset.range i)) → β =>
      fun j : Fin i => f ⟨j, Finset.mem_range.mpr j.2⟩) by fun_prop)
    (show Measurable (fun f : (j : ↑({i} : Finset ℕ)) → β =>
      f ⟨i, Finset.mem_singleton.mpr rfl⟩) by fun_prop)
  exact hc

lemma independent_past_event {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ℕ → Ω → β)
    (hW : ∀ i, Measurable (W i)) (hInd : iIndepFun W μ) (i : ℕ)
    (A : Set β) (G : Set (Fin i → β)) (hA : MeasurableSet A) (hG : MeasurableSet G) :
    μ.real {x | W i x ∈ A ∧ (fun j : Fin i => W j x) ∈ G} =
      μ.real (W i ⁻¹' A) * μ.real {x | (fun j : Fin i => W j x) ∈ G} := by
  have hh := (independent_past_current μ W hW hInd i).symm.measure_inter_preimage_eq_mul
    A G hA hG
  exact congrArg ENNReal.toReal hh |>.trans ENNReal.toReal_mul

lemma regeneration_span {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (n j : ℕ) (hj : j ≤ (regenerationWords ℓ X n).length) :
    X (regenerationTimes ℓ X n + j) = X (regenerationTimes ℓ X n) +
      wordPath 0 (regenerationWords ℓ X n) j := by
  have hh := (hX n).2.1 j hj
  rw [iterate_renewSuffix_eq ℓ X h0] at hh
  exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)

lemma regeneration_height_sum {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (n : ℕ) : dot (realPosition (X (regenerationTimes ℓ X n))) ℓ =
      ∑ i ∈ Finset.range n, wordHeightGain ℓ (regenerationWords ℓ X i) := by
  induction n with
  | zero => simp [h0, dot, realPosition]
  | succ n ih =>
    rw [regenerationTimes_succ, regeneration_span ℓ X h0 hX n _ (by rfl),
      dot_realPosition_add, ih, Finset.sum_range_succ, wordHeightGain]

lemma regeneration_radius_sum {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (n : ℕ) : ‖latticeVector (X (regenerationTimes ℓ X n))‖ ≤
      ∑ i ∈ Finset.range n, wordRadius (regenerationWords ℓ X i) := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [regenerationTimes_succ, regeneration_span ℓ X h0 hX n _ (by rfl),
      latticeVector_add, Finset.sum_range_succ]
    exact (norm_add_le _ _).trans (add_le_add ih (wordRadius_bound _ (by rfl)))

lemma regeneration_word_admissible {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (n : ℕ) : AdmissibleTrueWord ℓ (regenerationWords ℓ X n) :=
  ((firstTrueWord_characterization ℓ _ _ (hX n).2.1).mp ⟨(hX n).1, (hX n).2.2⟩).1

lemma regeneration_span_bounds {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (n j : ℕ) (hj : j ≤ (regenerationWords ℓ X n).length) :
    (dot (realPosition (X (regenerationTimes ℓ X n))) ℓ ≤
      dot (realPosition (X (regenerationTimes ℓ X n + j))) ℓ ∧
    dot (realPosition (X (regenerationTimes ℓ X n + j))) ℓ ≤
      dot (realPosition (X (regenerationTimes ℓ X (n+1)))) ℓ) ∧
    ‖latticeVector (X (regenerationTimes ℓ X n + j))‖ ≤
      (∑ i ∈ Finset.range n, wordRadius (regenerationWords ℓ X i)) +
        wordRadius (regenerationWords ℓ X n) := by
  have hw := regeneration_word_admissible ℓ X hX n
  have hlo : 0 ≤ dot (realPosition (wordPath 0 (regenerationWords ℓ X n) j)) ℓ := by
    rcases lt_or_eq_of_le hj with hj' | rfl
    · exact (hw.2.1 j hj').1
    · exact (wordHeightGain_positive ℓ _ hw).le
  have hhi : dot (realPosition (wordPath 0 (regenerationWords ℓ X n) j)) ℓ ≤
      wordHeightGain ℓ (regenerationWords ℓ X n) := by
    rcases lt_or_eq_of_le hj with hj' | rfl
    · exact (hw.2.1 j hj').2.le
    · rfl
  rw [regeneration_span ℓ X h0 hX n j hj, dot_realPosition_add, latticeVector_add]
  constructor
  · rw [regenerationTimes_succ, regeneration_span ℓ X h0 hX n _ (by rfl), dot_realPosition_add]
    exact ⟨le_add_of_nonneg_right hlo, add_le_add (le_refl _) hhi⟩
  · exact (norm_add_le _ _).trans
      (add_le_add (regeneration_radius_sum ℓ X h0 hX n) (wordRadius_bound _ hj))

lemma increasing_cuts_cover (T : ℕ → ℕ) (hT : StrictMono T) (h0 : T 0 = 0) (j : ℕ) :
    ∃ n, T n ≤ j ∧ j < T (n+1) := by
  have hex : ∃ n, j < T n := ⟨j+1, lt_of_lt_of_le (by omega) hT.le_apply⟩
  let n := Nat.find hex
  have hn : j < T n := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    simp [this, h0] at hn
  refine ⟨n-1, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by dsimp only [n] at hn0 ⊢; omega))
  · simpa only [Nat.sub_add_cancel hn0] using hn

lemma regeneration_prefix_radius {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    {K j : ℕ} (hj : j ≤ regenerationTimes ℓ X K) :
    ‖latticeVector (X j)‖ ≤ ∑ i ∈ Finset.range K, wordRadius (regenerationWords ℓ X i) := by
  rcases lt_or_eq_of_le hj with hj' | rfl
  · obtain ⟨n, hn, hn'⟩ := increasing_cuts_cover (regenerationTimes ℓ X)
      (regenerationTimes_strictMono ℓ X hX) (regenerationTimes_zero ℓ X) j
    have hnK : n < K := (regenerationTimes_strictMono ℓ X hX).lt_iff_lt.mp (hn.trans_lt hj')
    have hh := (regeneration_span_bounds ℓ X h0 hX n (j-regenerationTimes ℓ X n)
      (by rw [regenerationTimes_succ] at hn'; omega)).2
    rw [Nat.add_sub_of_le hn, ← Finset.sum_range_succ] at hh
    exact hh.trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega : n+1 ≤ K)) (fun _ _ _ => wordRadius_nonneg _))
  · exact regeneration_radius_sum ℓ X h0 hX K

lemma regeneration_prefix_height {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    {K j : ℕ} (hj : j ≤ regenerationTimes ℓ X K) :
    0 ≤ dot (realPosition (X j)) ℓ ∧
      dot (realPosition (X j)) ℓ ≤ ∑ i ∈ Finset.range K,
        wordHeightGain ℓ (regenerationWords ℓ X i) := by
  have ht := regenerationTimes_true ℓ X h0 hX K
  have hnd := (hX 0).1 j
  have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot, realPosition]
  change dot (realPosition (0 : Lattice d)) ℓ ≤ dot (realPosition (X j)) ℓ at hnd
  rw [hzero] at hnd
  refine ⟨hnd, ?_⟩
  rw [← regeneration_height_sum ℓ X h0 hX K]
  rcases lt_or_eq_of_le hj with hj' | rfl
  · exact (ht.1 j hj').le
  · rfl

lemma truncatedMean_increment_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    (t-s) * μ.real {x | t < f x} ≤ truncatedMean μ f t - truncatedMean μ f s ∧
    truncatedMean μ f t - truncatedMean μ f s ≤ (t-s) * μ.real {x | s < f x} := by
  have hms : MeasurableSet {x | s < f x} := measurableSet_lt measurable_const hf
  have hmt : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hf
  have his := integrable_min_nonneg μ f hf hfn s hs
  have hit := integrable_min_nonneg μ f hf hfn t (hs.trans hst)
  have he : truncatedMean μ f t - truncatedMean μ f s =
      ∫ x, min (f x) t - min (f x) s ∂μ := by
    rw [integral_sub hit his]; rfl
  rw [he]
  constructor
  · have hb := integral_mono ((integrable_const (t-s)).indicator hmt) (hit.sub his)
      (show ∀ x, Set.indicator {x | t < f x} (fun _ => t-s) x ≤
          min (f x) t - min (f x) s from by
        intro x
        by_cases hx : t < f x
        · simp only [Set.indicator_of_mem (show x ∈ {x | t < f x} from hx), min_eq_right hx.le,
            min_eq_right (hst.trans hx.le), le_refl]
        · rw [Set.indicator_of_notMem (show x ∉ {x | t < f x} from hx)]
          exact sub_nonneg.mpr (min_le_min le_rfl hst))
    simpa only [integral_indicator_const (t-s) hmt, smul_eq_mul, mul_comm, Pi.sub_apply] using hb
  · have hb := integral_mono (hit.sub his) ((integrable_const (t-s)).indicator hms)
      (show ∀ x, min (f x) t - min (f x) s ≤
          Set.indicator {x | s < f x} (fun _ => t-s) x from by
        intro x
        by_cases hx : s < f x
        · rw [Set.indicator_of_mem (show x ∈ {x | s < f x} from hx), min_eq_right hx.le]
          exact sub_le_sub_right (min_le_right _ _) _
        · rw [Set.indicator_of_notMem (show x ∉ {x | s < f x} from hx), min_eq_left (le_of_not_gt hx),
            min_eq_left ((le_of_not_gt hx).trans hst), sub_self])
    simpa only [integral_indicator_const (t-s) hms, smul_eq_mul, mul_comm, Pi.sub_apply] using hb

lemma scaled_tail_sum_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 ≤ a) {m n : ℕ} (hmn : m ≤ n) :
    truncatedMean μ f (a*n) - truncatedMean μ f (a*m) ≤
      a * ∑ i ∈ Finset.Ico m n, μ.real {x | a*i < f x} := by
  have hb : ∀ i : ℕ, truncatedMean μ f (a*(i+1)) - truncatedMean μ f (a*i) ≤
      a * μ.real {x | a*i < f x} := by
    intro i
    have hh := (truncatedMean_increment_bounds μ f hf hfn
      (mul_nonneg ha (Nat.cast_nonneg i)) (by nlinarith : a*i ≤ a*(i+1))).2
    convert hh using 1; ring
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.Ico m n) => hb i)
  have he := Finset.sum_Ico_sub (fun i : ℕ => truncatedMean μ f (a*i)) hmn
  simp only [Nat.cast_add, Nat.cast_one] at he
  rw [he, ← Finset.mul_sum] at hh
  exact hh

lemma scaled_tail_sum_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    a * ∑ i ∈ Finset.range n, μ.real {x | a*(i+1) < f x} ≤
      truncatedMean μ f (a*n) := by
  have hb : ∀ i : ℕ, a * μ.real {x | a*(i+1) < f x} ≤
      truncatedMean μ f (a*(i+1)) - truncatedMean μ f (a*i) := by
    intro i
    have hh := (truncatedMean_increment_bounds μ f hf hfn
      (mul_nonneg ha (Nat.cast_nonneg i)) (by nlinarith : a*i ≤ a*(i+1))).1
    convert hh using 1; ring
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range n) => hb i)
  have he := Finset.sum_range_sub (fun i : ℕ => truncatedMean μ f (a*i)) n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero] at he
  rw [← Finset.mul_sum, he] at hh
  have hz : truncatedMean μ f 0 = 0 := by
    simp only [truncatedMean, min_eq_right (hfn _), integral_zero]
  rwa [hz, sub_zero] at hh

lemma summable_positive_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (hint : Integrable f μ) :
    Summable (fun i : ℕ => μ.real {x | (i : ℝ) < f x}) := by
  apply (summable_nat_add_iff 1).mp
  apply summable_of_sum_range_le (fun _ => measureReal_nonneg)
  intro n
  have hb := scaled_tail_sum_upper μ f hf hfn (show (0:ℝ) ≤ 1 by norm_num) n
  have hu : truncatedMean μ f (1*n) ≤ ∫ x, f x ∂μ :=
    integral_mono (integrable_min_nonneg μ f hf hfn _ (by positivity)) hint
      (fun x => min_le_left _ _)
  simpa only [one_mul, Nat.cast_add, Nat.cast_one] using hb.trans hu

lemma positive_tail_sums_eventually_small {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) (hint : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ n, (∑ i ∈ Finset.Ico m n,
      μ.real {x | (i : ℝ) < f x}) < ε := by
  have hs := summable_positive_tail μ f hf hfn hint
  have ht := (tendsto_sum_nat_add (fun i : ℕ => μ.real {x | (i : ℝ) < f x})).eventually
    (Iio_mem_nhds hε)
  filter_upwards [ht] with m hm n
  rw [Finset.sum_Ico_eq_sum_range]
  have hh := ((summable_nat_add_iff m).mpr hs).sum_le_tsum (Finset.range (n-m))
    (fun _ _ => measureReal_nonneg)
  have he : (∑ i ∈ Finset.range (n-m), μ.real {x | ((m+i : ℕ) : ℝ) < f x}) =
      ∑ i ∈ Finset.range (n-m), μ.real {x | ((i+m : ℕ) : ℝ) < f x} := by
    apply Finset.sum_congr rfl; intro i _; rw [Nat.add_comm]
  rw [he]
  exact hh.trans_lt hm

lemma restricted_large_word_intensity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (R L : Ω → ℝ) (hR : Measurable R)
    (hRn : ∀ x, 0 ≤ R x) {a B η : ℝ} (ha : 0 < a) (hB : 1 ≤ B)
    {m N : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N+1)
    (hlo : η*a ≤ truncatedMean μ R (a*N))
    (hhi : truncatedMean μ R (a*N) < 2*η*a)
    (hbase : truncatedMean μ R (B*a*m) < η*a/4)
    (hwidth : (∑ i ∈ Finset.Ico m (N+1), μ.real {x | (i:ℝ) < L x}) < η/(4*B)) :
    η/(2*B) ≤ (∑ i ∈ Finset.Ico m (N+1),
      μ.real {x | B*a*i < R x ∧ L x ≤ (i:ℝ)}) ∧
    (∑ i ∈ Finset.Ico m (N+1),
      μ.real {x | B*a*i < R x ∧ L x ≤ (i:ℝ)}) < 2*η := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBa : 0 < B*a := mul_pos hBpos ha
  let S := Finset.Ico m (N+1)
  let lam := ∑ i ∈ S, μ.real {x | B*a*i < R x ∧ L x ≤ (i:ℝ)}
  have hlose : (∑ i ∈ S, μ.real {x | B*a*i < R x}) ≤
      lam + ∑ i ∈ S, μ.real {x | (i:ℝ) < L x} := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ μ.real ({x | B*a*i < R x ∧ L x ≤ (i:ℝ)} ∪ {x | (i:ℝ) < L x}) := by
        apply measureReal_mono (μ := μ)
        intro x hx
        by_cases hl : L x ≤ (i:ℝ)
        · exact Or.inl ⟨hx,hl⟩
        · exact Or.inr (lt_of_not_ge hl)
      _ ≤ _ := measureReal_union_le _ _
  have hlow := scaled_tail_sum_lower μ R hR hRn hBa.le hmN
  have hmon : truncatedMean μ R (a*N) ≤ truncatedMean μ R (B*a*(N+1)) := by
    apply truncatedMean_mono μ R hR hRn (by positivity)
    have he : a*N ≤ B*(a*N) := le_mul_of_one_le_left (by positivity) hB
    nlinarith
  have hupper0 : (∑ i ∈ S, μ.real {x | B*a*i < R x ∧ L x ≤ (i:ℝ)}) ≤
      ∑ i ∈ Finset.Ico 1 (N+1), μ.real {x | B*a*i < R x} := by
    calc
      _ ≤ ∑ i ∈ S, μ.real {x | B*a*i < R x} :=
        Finset.sum_le_sum (fun _ _ => measureReal_mono (μ := μ) (fun _ hx => hx.1))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi => Finset.mem_Ico.mpr ⟨hm.trans (Finset.mem_Ico.mp hi).1,(Finset.mem_Ico.mp hi).2⟩)
        (fun _ _ _ => measureReal_nonneg)
  have he : (∑ i ∈ Finset.Ico 1 (N+1), μ.real {x | B*a*i < R x}) =
      ∑ i ∈ Finset.range N, μ.real {x | B*a*(i+1) < R x} := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_comm (1:ℝ)]
  rw [he] at hupper0
  have hupper1 := scaled_tail_sum_upper μ R hR hRn hBa.le N
  have hupper2 := truncatedMean_mul_le μ R hR hRn
    (show 0 ≤ a*N by positivity) hB
  rw [← mul_assoc] at hupper2
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 2*B)).mpr
    have hw := (lt_div_iff₀ (by positivity : 0 < 4*B)).mp hwidth
    have hmnow := mul_le_mul_of_nonneg_left hlose hBa.le
    change (B*a)*(∑ i ∈ S, μ.real {x | B*a*i < R x}) ≤ (B*a)*(lam+_) at hmnow
    have haN : B*a*(N+1 : ℕ) = B*a*(N+1) := by push_cast; rfl
    rw [haN] at hlow
    dsimp only [S] at hmnow
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hupper0 hBa.le
    have hhh := mul_lt_mul_of_pos_left hhi hBpos
    nlinarith

lemma independent_rare_word_past {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : ℕ → Ω → β)
    (hW : ∀ i, Measurable (W i)) (hInd : iIndepFun W μ)
    (S : Finset ℕ) (A : ℕ → Set β) (G : (i : ℕ) → Set (Fin i → β))
    (hA : ∀ i, MeasurableSet (A i)) (hG : ∀ i, MeasurableSet (G i))
    (q : ℝ) (hprev : ∀ i ∈ S, q ≤ μ.real {x | (fun j : Fin i => W j x) ∈ G i}) :
    q * (∑ i ∈ S, μ.real (W i ⁻¹' A i)) -
      (∑ i ∈ S, μ.real (W i ⁻¹' A i))^2 / 2 ≤
      μ.real {x | ∃ i ∈ S, W i x ∈ A i ∧ (fun j : Fin i => W j x) ∈ G i} := by
  apply independent_rare_words_lower_bound μ S
    (fun i => W i ⁻¹' A i) (fun i => (fun x j => W (j : Fin i) x) ⁻¹' G i)
    (fun i => (hA i).preimage (hW i)) (fun i => (hG i).preimage (by fun_prop))
    q
  · intro i hi
    rw [show (W i ⁻¹' A i) ∩ ((fun x j => W (j : Fin i) x) ⁻¹' G i) =
        {x | W i x ∈ A i ∧ (fun j : Fin i => W j x) ∈ G i} from rfl,
      independent_past_event μ W hW hInd i (A i) (G i) (hA i) (hG i), mul_comm]
    exact mul_le_mul_of_nonneg_left (hprev i hi) measureReal_nonneg
  · intro i _ j _ hij
    have hh := (hInd.indepFun hij).measure_inter_preimage_eq_mul (A i) (A j) (hA i) (hA j)
    exact congrArg ENNReal.toReal hh |>.trans ENNReal.toReal_mul

lemma polynomial_lower_from_small_intensity {B η lam p : ℝ}
    (hB : 0 < B) (hη : 0 < η) (hηsmall : η ≤ 1/10)
    (hlow : η/(2*B) ≤ lam) (hupper : lam ≤ 2*η)
    (hp : (4/5)*lam - lam^2/2 ≤ p) : η/(4*B) ≤ p := by
  have hlam : 0 ≤ lam := (div_pos hη (by positivity)).le.trans hlow
  have hsmall : lam ≤ 1/5 := by linarith
  have hprod := mul_le_mul_of_nonneg_left hsmall hlam
  have he : η/(4*B) = (η/(2*B))/2 := by field_simp; ring
  rw [he]
  nlinarith

def WordTemplate {d : ℕ} (ℓ : Vector d) (c C C0 a : ℝ) (K : ℕ) : Set (Path d) :=
  {X | ∀ k ≤ K,
    (c*k-C0 ≤ ∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j)) ∧
    ((∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j)) ≤ C*k+C0) ∧
    ((∑ j ∈ Finset.range k, wordRadius (regenerationWords ℓ X j)) ≤ a*k)}

lemma measurableSet_wordTemplate {d : ℕ} (ℓ : Vector d) (c C C0 a : ℝ) (K : ℕ) :
    MeasurableSet (WordTemplate ℓ c C C0 a K) := by
  simp only [WordTemplate, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro _
  have hL : Measurable (fun X => ∑ j ∈ Finset.range k,
      wordHeightGain ℓ (regenerationWords ℓ X j)) :=
    Finset.measurable_fun_sum _ fun j _ =>
      (measurable_of_countable (wordHeightGain ℓ)).comp (measurable_regenerationWord ℓ j)
  have hR : Measurable (fun X => ∑ j ∈ Finset.range k,
      wordRadius (regenerationWords ℓ X j)) :=
    Finset.measurable_fun_sum _ fun j _ => measurable_wordRadius.comp (measurable_regenerationWord ℓ j)
  exact (measurableSet_le measurable_const hL).inter
    ((measurableSet_le hL measurable_const).inter (measurableSet_le hR measurable_const))

lemma wordTemplate_antitone {d : ℕ} (ℓ : Vector d) (c C C0 a : ℝ) {K M : ℕ} (hKM : K ≤ M) :
    WordTemplate ℓ c C C0 a M ⊆ WordTemplate ℓ c C C0 a K :=
  fun _ hX k hk => hX k (hk.trans hKM)

lemma controlled_template_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (c C C0 η a : ℝ) (ha : 0 < a) (C1 N : ℕ) (hC1 : 1 ≤ C1)
    (hheight : (19/20 : ℝ) < (conditionedLaw ν ℓ).real {X | ∀ k : ℕ,
      c*k-C0 ≤ ∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j) ∧
      (∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j)) ≤ C*k+C0})
    (hsmall : 4*C1*η < 1/10)
    (hI : truncatedMean (conditionedLaw ν ℓ) (fun X => wordRadius (firstWord ℓ X)) (a*N) < 2*η*a) :
    (4/5 : ℝ) < (conditionedLaw ν ℓ).real (WordTemplate ℓ c C C0 a (C1*N)) := by
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let E : Set (Path d) := {X | ∀ k : ℕ,
    c*k-C0 ≤ ∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j) ∧
      (∑ j ∈ Finset.range k, wordHeightGain ℓ (regenerationWords ℓ X j)) ≤ C*k+C0}
  let F : Set (Path d) := {X | ∃ k, 0 < k ∧ k ≤ C1*N ∧
    a*k < ∑ j ∈ Finset.range k, wordRadius (regenerationWords ℓ X j)}
  have hf : μ.real F < 4*C1*η := truncated_template_failure_bound μ _
    (renewSuffix_preserves_conditioned ν ℓ htrans) _
    (measurable_wordRadius.comp (measurable_firstWord ℓ)) (fun _ => wordRadius_nonneg _)
    η a ha C1 N hC1 hI
  have hsub : E ⊆ WordTemplate ℓ c C C0 a (C1*N) ∪ F := by
    intro X hX
    by_cases hF : X ∈ F
    · exact Or.inr hF
    · left
      intro k hk
      refine ⟨(hX k).1,(hX k).2, ?_⟩
      by_contra h
      have hk0 : 0 < k := by
        by_contra hk0
        have he : k = 0 := by omega
        simp [he] at h
      exact hF ⟨k,hk0,hk,lt_of_not_ge h⟩
  have hu := (measureReal_mono (μ := μ) hsub).trans (measureReal_union_le _ _)
  change 19/20 < μ.real E at hheight
  change 4/5 < μ.real (WordTemplate ℓ c C C0 a (C1*N))
  linarith

lemma wordTemplate_congr {d : ℕ} (ℓ : Vector d) (c C C0 a : ℝ) (K : ℕ)
    {X Y : Path d} (h : ∀ j < K, regenerationWords ℓ X j = regenerationWords ℓ Y j) :
    X ∈ WordTemplate ℓ c C C0 a K ↔ Y ∈ WordTemplate ℓ c C C0 a K := by
  have he (k : ℕ) (hk : k ≤ K) (f : List (Direction d) → ℝ) :
      (∑ j ∈ Finset.range k, f (regenerationWords ℓ X j)) =
      ∑ j ∈ Finset.range k, f (regenerationWords ℓ Y j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [h j ((Finset.mem_range.mp hj).trans_le hk)]
  simp only [WordTemplate, Set.mem_ofPred_eq]
  constructor <;> intro hh k hk
  · simpa only [← he k hk (wordHeightGain ℓ), ← he k hk wordRadius] using hh k hk
  · simpa only [he k hk (wordHeightGain ℓ), he k hk wordRadius] using hh k hk

lemma current_word_template_independent {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (c C C0 a : ℝ) (i : ℕ) (A : Set (List (Direction d))) :
    (conditionedLaw ν ℓ).real ({X | regenerationWords ℓ X i ∈ A} ∩
      WordTemplate ℓ c C C0 a i) =
    (conditionedLaw ν ℓ).real {X | regenerationWords ℓ X i ∈ A} *
      (conditionedLaw ν ℓ).real (WordTemplate ℓ c C C0 a i) := by
  let μ := conditionedLaw ν ℓ
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  let G : Set (Fin i → List (Direction d)) := {v | ∃ X ∈ WordTemplate ℓ c C C0 a i,
    ∀ j : Fin i, v j = regenerationWords ℓ X j}
  have he (X : Path d) : (fun j : Fin i => regenerationWords ℓ X j) ∈ G ↔
      X ∈ WordTemplate ℓ c C C0 a i := by
    constructor
    · rintro ⟨Y,hY,hXY⟩
      exact (wordTemplate_congr ℓ c C C0 a i (fun j hj => hXY ⟨j,hj⟩)).mpr hY
    · intro hX
      exact ⟨X,hX,fun _ => rfl⟩
  have hh := independent_past_event μ (fun j X => regenerationWords ℓ X j)
    (measurable_regenerationWord ℓ) (regenerationWords_independent ν ℓ htrans) i A G
    (Set.to_countable _).measurableSet (Set.to_countable _).measurableSet
  simpa only [he, Set.ofPred_mem_eq, Set.inter_def, Set.mem_ofPred_eq, Set.preimage, μ] using hh

end DirectionalTransience
end
end

end OAI
