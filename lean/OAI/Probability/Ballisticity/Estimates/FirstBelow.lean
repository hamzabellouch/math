import Mathlib
import OAI.Probability.Ballisticity.Crossings.Hit

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma endpointLaw_small_ratio {d : ℕ} (ℓ : Vector d) (x : Lattice d) {H : ℝ} (hH : 0 ≤ H)
    (ω : Environment d) {s : ℝ≥0} (hs : 0 < s)
    (hq : noDropQuenched ℓ x ω < (s : ℝ≥0∞) * crossingQuenched ℓ x H ω) :
    (1 : ℝ≥0∞) ≤ 2 * endpointLaw ℓ x H ω {y | noDropQuenched ℓ y ω ≤ 2 * (s : ℝ≥0∞)} := by
  have ha : crossingQuenched ℓ x H ω ≠ 0 := by
    intro he
    rw [he, mul_zero] at hq
    exact not_lt_zero hq
  let : IsProbabilityMeasure (endpointLaw ℓ x H ω) := ⟨endpointLaw_total ℓ x H ω ha⟩
  apply mass_of_small_mean _ _ (measurable_of_countable _) hs
  apply (endpointLaw_mean_le ℓ x hH ω).trans
  exact le_of_lt ((ENNReal.div_lt_iff (Or.inl ha)
    (Or.inl (crossingQuenched_ne_top ℓ x H ω))).mpr hq)

lemma measurable_endpointLaw_rows {d : ℕ} (ℓ : Vector d) (x : Lattice d) {H : ℝ} (hH : 0 < H)
    (U : Set (Lattice d)) :
    @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (fun ω => endpointLaw ℓ x H ω U) := by
  simp only [endpointLaw, Measure.smul_apply, smul_eq_mul]
  exact (measurable_crossingQuenched_rows ℓ x hH).inv.mul
    ((Measure.measurable_coe U.to_countable.measurableSet).comp
      (measurable_hitKernel_rows _ _ x ⟨le_rfl, by linarith⟩))

lemma endpointLaw_supported {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    (ω : Environment d) {y : Lattice d} (hy : y ∉ Upper ℓ x H) :
    endpointLaw ℓ x H ω {y} = 0 := by
  rw [endpointLaw, Measure.smul_apply, smul_eq_mul, hitKernel_apply]
  have he : Upper ℓ x H ∩ {y} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain rfl := hz.2
    exact hy hz.1
  rw [he]
  have he' (n : ℕ) : HitAt (Strip ℓ x H) ∅ n = ∅ := by
    ext X
    simp [HitAt]
  simp only [he', measure_empty, tsum_zero, mul_zero]

lemma noDropQuenched_small_translation {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (y : Lattice d) (c : ℝ≥0∞) :
    environmentLaw ν {ω | noDropQuenched ℓ y ω ≤ c} =
      environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ c} := by
  have he := congrArg (fun μ : Measure (Environment d) =>
    μ {ω | noDropQuenched ℓ 0 ω ≤ c}) (environment_translation ν y)
  rw [Measure.map_apply (by fun_prop)
    (measurableSet_le (measurable_noDropQuenched ℓ 0) measurable_const)] at he
  convert he using 1
  congr 1
  ext ω
  change noDropQuenched ℓ y ω ≤ c ↔ noDropQuenched ℓ 0 (fun a => ω (y + a)) ≤ c
  rw [noDropQuenched_translation]

lemma endpointLaw_badmass {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) {H : ℝ} (hH : 0 < H)
    {A : Set (Environment d)} (hA : MeasurableSet[rowSigma (Strip ℓ x H)] A)
    (c : ℝ≥0∞) :
    (∫⁻ ω, A.indicator (fun ω => endpointLaw ℓ x H ω
      {y | noDropQuenched ℓ y ω ≤ c}) ω ∂environmentLaw ν) ≤
      environmentLaw ν A * environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ c} := by
  let w := fun (y : Lattice d) => A.indicator (fun ω => endpointLaw ℓ x H ω {y})
  let B := fun y : Lattice d => {ω | noDropQuenched ℓ y ω ≤ c}
  have hw (y : Lattice d) : @Measurable _ _ (rowSigma (Strip ℓ x H)) _ (w y) :=
    (measurable_endpointLaw_rows ℓ x hH {y}).indicator hA
  have hB (y : Lattice d) : MeasurableSet (B y) :=
    measurableSet_le (measurable_noDropQuenched ℓ y) measurable_const
  have hwB (y : Lattice d) : Measurable (fun ω => w y ω * (B y).indicator 1 ω) :=
    ((hw y).mono (rowSigma_le _) le_rfl).mul (measurable_const.indicator (hB y))
  have he (ω : Environment d) :
      A.indicator (fun ω => endpointLaw ℓ x H ω {y | noDropQuenched ℓ y ω ≤ c}) ω =
        ∑' y, w y ω * (B y).indicator 1 ω := by
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω, ← Measure.tsum_indicator_apply_singleton _ _
        (Set.to_countable _).measurableSet]
      apply tsum_congr
      intro y
      by_cases hy : noDropQuenched ℓ y ω ≤ c
      · simp [w, B, hω, hy]
      · simp [w, B, hω, hy]
    · simp [w, hω]
  simp_rw [he]
  rw [lintegral_tsum (fun y => (hwB y).aemeasurable)]
  have hf (y : Lattice d) :
      (∫⁻ ω, w y ω * (B y).indicator 1 ω ∂environmentLaw ν) =
        (∫⁻ ω, w y ω ∂environmentLaw ν) *
          environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ c} := by
    by_cases hy : y ∈ Upper ℓ x H
    · have hST : Disjoint (Strip ℓ x H)
          {z | dot (realPosition y) ℓ ≤ dot (realPosition z) ℓ} := by
        apply Set.disjoint_left.mpr
        intro z hz hz'
        have hy' : dot (realPosition x) ℓ + H ≤ dot (realPosition y) ℓ := hy
        exact (not_le_of_gt hz.2) (hy'.trans hz')
      have hmB : @Measurable _ _ (rowSigma {z | dot (realPosition y) ℓ ≤ dot (realPosition z) ℓ}) _
          ((B y).indicator (1 : Environment d → ℝ≥0∞)) :=
        measurable_const.indicator (measurableSet_le
          (measurable_noDropQuenched_rows ℓ y) measurable_const)
      rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
        (rowSigma_le _) (rowSigma_le _) (environment_indep_rows ν hST) (hw y) hmB,
        lintegral_indicator_one (hB y)]
      rw [noDropQuenched_small_translation ν ℓ y c]
    · have hew : w y = 0 := by
        funext ω
        change A.indicator (fun ω => endpointLaw ℓ x H ω {y}) ω = 0
        by_cases hω : ω ∈ A
        · rw [Set.indicator_of_mem hω, endpointLaw_supported ℓ x H ω hy]
        · exact Set.indicator_of_notMem hω _
      simp [hew]
  simp_rw [hf]
  rw [ENNReal.tsum_mul_right, ← lintegral_tsum
    (fun y => ((hw y).mono (rowSigma_le _) le_rfl).aemeasurable)]
  apply mul_le_mul' _ le_rfl
  calc
    (∫⁻ ω, ∑' y, w y ω ∂environmentLaw ν) ≤ ∫⁻ ω, A.indicator 1 ω ∂environmentLaw ν := by
      apply lintegral_mono
      intro ω
      by_cases hω : ω ∈ A
      · simp only [w, Set.indicator_of_mem hω, Pi.one_apply]
        have hh := Measure.tsum_indicator_apply_singleton (endpointLaw ℓ x H ω) Set.univ MeasurableSet.univ
        simp only [Set.indicator_univ] at hh
        rw [hh]
        exact endpointLaw_total_le_one ℓ x H ω
      · simp [w, hω]
    _ = environmentLaw ν A := lintegral_indicator_one (rowSigma_le _ _ hA)

lemma stopped_layer_small_ratio {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) {H : ℝ} (hH : 0 < H)
    {A : Set (Environment d)} (hA : MeasurableSet[rowSigma (Strip ℓ x H)] A)
    {s : ℝ≥0} (hs : 0 < s) :
    environmentLaw ν (A ∩ {ω | noDropQuenched ℓ x ω <
      (s : ℝ≥0∞) * crossingQuenched ℓ x H ω}) ≤
        2 * environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ 2 * (s : ℝ≥0∞)} *
          environmentLaw ν A := by
  let E := {ω | noDropQuenched ℓ x ω < (s : ℝ≥0∞) * crossingQuenched ℓ x H ω}
  have hE : MeasurableSet E := measurableSet_lt (measurable_noDropQuenched ℓ x)
    (measurable_const.mul ((measurable_crossingQuenched_rows ℓ x hH).mono (rowSigma_le _) le_rfl))
  have hA' : MeasurableSet A := rowSigma_le _ _ hA
  rw [← lintegral_indicator_one (hA'.inter hE)]
  calc
    (∫⁻ ω, (A ∩ E).indicator 1 ω ∂environmentLaw ν) ≤
        ∫⁻ ω, 2 * A.indicator (fun ω => endpointLaw ℓ x H ω
          {y | noDropQuenched ℓ y ω ≤ 2 * (s : ℝ≥0∞)}) ω ∂environmentLaw ν := by
      apply lintegral_mono
      intro ω
      change (A ∩ E).indicator 1 ω ≤ 2 * A.indicator (fun ω => endpointLaw ℓ x H ω
        {y | noDropQuenched ℓ y ω ≤ 2 * (s : ℝ≥0∞)}) ω
      by_cases hω : ω ∈ A ∩ E
      · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω.1]
        exact endpointLaw_small_ratio ℓ x hH.le ω hs hω.2
      · rw [Set.indicator_of_notMem hω]
        exact zero_le
    _ = 2 * ∫⁻ ω, A.indicator (fun ω => endpointLaw ℓ x H ω
          {y | noDropQuenched ℓ y ω ≤ 2 * (s : ℝ≥0∞)}) ω ∂environmentLaw ν :=
      lintegral_const_mul' _ _ ENNReal.ofNat_ne_top
    _ ≤ 2 * (environmentLaw ν A *
        environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ 2 * (s : ℝ≥0∞)}) :=
      mul_le_mul' le_rfl (endpointLaw_badmass ν ℓ x hH hA _)
    _ = _ := by ac_rfl

def FirstBelow {α : Type*} [Preorder α] (a : ℕ → α) (t : α) (n : ℕ) : Prop :=
  a n < t ∧ ∀ k < n, t ≤ a k

lemma firstBelow_iff_exists {α : Type*} [LinearOrder α] (a : ℕ → α) (t : α) :
    (∃ n, FirstBelow a t n) ↔ ∃ n, a n < t := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn.1⟩
  · intro h
    exact ⟨Nat.find h, Nat.find_spec h, fun k hk => le_of_not_gt (Nat.find_min h hk)⟩

lemma firstBelow_unique {α : Type*} [LinearOrder α] {a : ℕ → α} {t : α} {n m : ℕ}
    (hn : FirstBelow a t n) (hm : FirstBelow a t m) : n = m := by
  rcases lt_trichotomy n m with h | h | h
  · exact False.elim ((not_lt_of_ge (hm.2 n h)) hn.1)
  · exact h
  · exact False.elim ((not_lt_of_ge (hn.2 m h)) hm.1)

lemma firstBelow_pairwise_disjoint {α β : Type*} [LinearOrder β] (a : ℕ → α → β) (t : β) :
    Pairwise (fun n m => Disjoint {ω | FirstBelow (fun k => a k ω) t n}
      {ω | FirstBelow (fun k => a k ω) t m}) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro ω hn hm
  exact hnm (firstBelow_unique (a := fun k => a k ω) hn hm)

lemma crossingQuenched_mesh_tendsto {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (ω : Environment d) {m : ℝ} (hm : 0 < m)
    (htrans : ∀ᵐ X ∂quenchedKernel (ω, x), X ∈ TransientPaths ℓ) :
    Tendsto (fun n : ℕ => crossingQuenched ℓ x (n * m) ω) atTop
      (𝓝 (noDropQuenched ℓ x ω)) := by
  have he : (⋂ n : ℕ, Cross ℓ x (n * m)) =ᵐ[quenchedKernel (ω, x)] NoDrop ℓ x := by
    filter_upwards [htrans] with X hX
    apply propext
    constructor
    · intro h
      apply iInter_cross_subset_noDrop ℓ x
      apply Set.mem_iInter.mpr
      intro H
      obtain ⟨n, hn⟩ := exists_nat_ge ((H : ℝ) / m)
      exact cross_antitone ℓ x ((div_le_iff₀ hm).mp hn) (Set.mem_iInter.mp h n)
    · intro hD
      exact Set.mem_iInter.mpr fun n => noDrop_subset_cross_of_tendsto ℓ x X hX hD (n * m)
  have h := tendsto_measure_iInter_atTop
    (μ := quenchedKernel (ω, x)) (s := fun n : ℕ => Cross ℓ x (n * m))
    (fun n => (measurableSet_cross ℓ x (n * m)).nullMeasurableSet)
    (fun n k hnk => cross_antitone ℓ x (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnk) hm.le))
    ⟨0, measure_ne_top _ _⟩
  rw [measure_congr he] at h
  exact h

lemma measurableSet_firstBelow_crossing {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    {m : ℝ} (hm : 0 < m) (t : ℝ≥0∞) (n : ℕ) :
    MeasurableSet[rowSigma (Strip ℓ x (n * m))]
      {ω | FirstBelow (fun k => crossingQuenched ℓ x (k * m) ω) t n} := by
  have ha (k : ℕ) (hk : k ≤ n) :
      @Measurable _ _ (rowSigma (Strip ℓ x (n * m))) _ (crossingQuenched ℓ x (k * m)) := by
    by_cases hk0 : k = 0
    · subst k
      simp only [Nat.cast_zero, zero_mul]
      convert (measurable_const : @Measurable _ _ (rowSigma (Strip ℓ x (n * m))) _
        (fun _ : Environment d => (1 : ℝ≥0∞))) using 1
      funext ω
      exact crossingQuenched_zero ℓ x ω
    · apply (measurable_crossingQuenched_rows ℓ x (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)) hm)).mono
        (rowSigma_mono ?_) le_rfl
      intro y hy
      refine ⟨hy.1, hy.2.trans_le ?_⟩
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hm.le)
  change MeasurableSet[rowSigma (Strip ℓ x (n * m))]
    ({ω | crossingQuenched ℓ x (n * m) ω < t} ∩
      {ω | ∀ k < n, t ≤ crossingQuenched ℓ x (k * m) ω})
  apply MeasurableSet.inter (measurableSet_lt (ha n le_rfl) measurable_const)
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk =>
    measurableSet_le measurable_const (ha k hk.le)

lemma noDrop_small_recursive {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (he : 0 < dot (realPosition (step e)) ℓ)
    (htrans : DirectionallyTransient ν ℓ) {κ : ℝ≥0}
    (hκ : ∀ᵐ ω ∂environmentLaw ν, ∀ x, κ ≤ (ω x).1 e)
    {t r s : ℝ≥0} (ht : t < 1) (hrt : r ≤ t) (hs : 0 < s)
    (hr : r ≤ s * κ * t) :
    environmentLaw ν {ω | noDropQuenched ℓ 0 ω < (r : ℝ≥0∞)} ≤
      (2 * environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ 2 * (s : ℝ≥0∞)}) *
        environmentLaw ν {ω | noDropQuenched ℓ 0 ω < (t : ℝ≥0∞)} := by
  let m := dot (realPosition (step e)) ℓ
  let a := fun (n : ℕ) (ω : Environment d) => crossingQuenched ℓ 0 (n * m) ω
  let A := fun n => {ω | FirstBelow (fun k => a k ω) (t : ℝ≥0∞) n}
  let B := {ω | noDropQuenched ℓ 0 ω < (r : ℝ≥0∞)}
  let C := {ω | noDropQuenched ℓ 0 ω < (t : ℝ≥0∞)}
  let ρ := 2 * environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ 2 * (s : ℝ≥0∞)}
  have hAm (n : ℕ) : MeasurableSet (A n) := rowSigma_le _ _
    (measurableSet_firstBelow_crossing ℓ 0 he t n)
  have hB : MeasurableSet B := measurableSet_lt (measurable_noDropQuenched ℓ 0) measurable_const
  have hpair : Pairwise (fun n k => Disjoint (A n) (A k)) := firstBelow_pairwise_disjoint a t
  have hlim : ∀ᵐ ω ∂environmentLaw ν, Tendsto (fun n => a n ω) atTop (𝓝 (noDropQuenched ℓ 0 ω)) := by
    filter_upwards [quenched_directionallyTransient_ae ν ℓ htrans] with ω hω
    exact crossingQuenched_mesh_tendsto ℓ 0 ω he (hω 0)
  have hAC : (⋃ n, A n) =ᵐ[environmentLaw ν] C := by
    filter_upwards [hlim] with ω hω
    apply propext
    rw [Set.mem_iUnion]
    change (∃ n, FirstBelow (fun k => a k ω) (t : ℝ≥0∞) n) ↔ _
    rw [firstBelow_iff_exists (fun k => a k ω)]
    constructor
    · rintro ⟨n, hn⟩
      exact lt_of_le_of_lt ((show Antitone (fun k => a k ω) from fun i j hij =>
        crossingQuenched_antitone ℓ 0 ω (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) he.le)).le_of_tendsto hω n) hn
    · intro h
      exact (hω.eventually (eventually_lt_nhds h)).exists
  have hBA : (⋃ n, A n ∩ B) =ᵐ[environmentLaw ν] B := by
    filter_upwards [hAC] with ω hω
    apply propext
    constructor
    · intro h
      exact (Set.mem_iUnion.mp h).choose_spec.2
    · intro h
      have hc : ω ∈ C := lt_of_lt_of_le h (ENNReal.coe_le_coe.mpr hrt)
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hω.mpr hc)
      exact Set.mem_iUnion.mpr ⟨n, hn, h⟩
  have hstep (n : ℕ) : environmentLaw ν (A n ∩ B) ≤ ρ * environmentLaw ν (A n) := by
    by_cases hn : n = 0
    · subst n
      have heA : A 0 = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        have hh := hω.1
        simp only [a, Nat.cast_zero, zero_mul, crossingQuenched_zero] at hh
        exact (not_lt_of_ge (ENNReal.coe_le_coe.mpr ht.le)) hh
      simp [heA]
    · have hm : 0 < (n : ℝ) * m := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) he
      apply le_trans (measure_mono_ae (t := A n ∩ {ω | noDropQuenched ℓ 0 ω <
        (s : ℝ≥0∞) * a n ω}) ?_) (stopped_layer_small_ratio ν ℓ 0 hm
          (measurableSet_firstBelow_crossing ℓ 0 he t n) hs)
      filter_upwards [hκ] with ω hω
      intro h
      refine ⟨h.1, ?_⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hprev : (t : ℝ≥0∞) ≤ a k ω := h.1.2 k (Nat.lt_succ_self k)
      have hstep := crossingQuenched_lower_step ℓ ω 0 e hω
        (show 0 ≤ (k : ℝ) * m from mul_nonneg (Nat.cast_nonneg _) he.le)
      have hlow : (κ : ℝ≥0∞) * (t : ℝ≥0∞) ≤ a (k + 1) ω := by
        apply (mul_le_mul' le_rfl hprev).trans
        simpa [a, Nat.cast_add, Nat.cast_one, add_mul] using hstep
      exact lt_of_lt_of_le h.2 ((ENNReal.coe_le_coe.mpr hr).trans (by
        push_cast
        rw [mul_assoc]
        exact mul_le_mul' le_rfl hlow))
  change environmentLaw ν B ≤ ρ * environmentLaw ν C
  rw [← measure_congr hBA, measure_iUnion
    (fun i j hij => (hpair hij).mono Set.inter_subset_left Set.inter_subset_left)
    (fun n => (hAm n).inter hB)]
  calc
    ∑' n, environmentLaw ν (A n ∩ B) ≤ ∑' n, ρ * environmentLaw ν (A n) := ENNReal.tsum_le_tsum hstep
    _ = ρ * ∑' n, environmentLaw ν (A n) := ENNReal.tsum_mul_left
    _ = ρ * environmentLaw ν C := by rw [← measure_iUnion hpair hAm, measure_congr hAC]

lemma positive_random_small_set {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ≥0∞) (hf : Measurable f)
    (hp : ∀ᵐ x ∂μ, 0 < f x) :
    ∃ s : ℝ≥0, 0 < s ∧ s ≤ 1 / 4 ∧ μ {x | f x ≤ 2 * (s : ℝ≥0∞)} < 1 / 4 := by
  let b : ℝ≥0 := 1 / 2
  let E := fun n : ℕ => {x | f x ≤ ((b ^ n : ℝ≥0) : ℝ≥0∞)}
  have hE (n : ℕ) : MeasurableSet (E n) := measurableSet_le hf measurable_const
  have ha : Antitone E := by
    intro i j hij x hx
    exact hx.trans (ENNReal.coe_le_coe.mpr (pow_le_pow_right_of_le_one' (by norm_num [b]) hij))
  have he : (⋂ n, E n) =ᵐ[μ] (∅ : Set α) := by
    filter_upwards [hp] with x hx
    apply propext
    change (x ∈ ⋂ n, E n) ↔ False
    refine ⟨?_, False.elim⟩
    intro hn
    have hfb : f x ≤ 0 := ge_of_tendsto
      (show Tendsto (fun n : ℕ => ((b ^ n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) by
        simp only [ENNReal.coe_pow]
        exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num [b]))
      (Eventually.of_forall fun n => Set.mem_iInter.mp hn n)
    exact hx.not_ge hfb
  have hlim := tendsto_measure_iInter_atTop
    (fun n => (hE n).nullMeasurableSet) ha ⟨0, measure_ne_top μ _⟩
  rw [measure_congr he, measure_empty] at hlim
  obtain ⟨N, hN⟩ := (hlim.eventually (eventually_lt_nhds (show (0 : ℝ≥0∞) < 1 / 4 by norm_num))).exists
  refine ⟨b ^ N / 4, by positivity, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (pow_le_one₀ (show 0 ≤ b from bot_le) (by norm_num [b])) (by positivity)
  · apply lt_of_le_of_lt (measure_mono ?_) hN
    intro x hx
    change f x ≤ _ at hx
    change f x ≤ _
    apply hx.trans
    have hb : 2 * (b ^ N / 4) ≤ b ^ N := by
      have hbpos : 0 ≤ b ^ N := bot_le
      linarith
    exact_mod_cast hb

lemma noDrop_geometric_tail {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (e : Direction d)
    (he : 0 < dot (realPosition (step e)) ℓ) (htrans : DirectionallyTransient ν ℓ) :
    ∃ δ : ℝ≥0, ∃ ρ : ℝ≥0∞, 0 < δ ∧ δ < 1 ∧ ρ < 1 ∧
      ∀ j : ℕ, environmentLaw ν {ω | noDropQuenched ℓ 0 ω < ((δ ^ (j + 1) : ℝ≥0) : ℝ≥0∞)} ≤ ρ ^ j := by
  obtain ⟨κ, hκ, hκae⟩ := environment_uniform_elliptic ν hue
  have hκle : κ ≤ 1 := by
    obtain ⟨ω, hω⟩ := hκae.exists
    exact (hω 0 e).trans (row_entry_le_one _ e)
  have hp := noDropQuenched_positive_ae ν hue ℓ e he
    (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  obtain ⟨s, hs, hsle, hsμ⟩ := positive_random_small_set (environmentLaw ν)
    (noDropQuenched ℓ 0) (measurable_noDropQuenched ℓ 0) (hp.mono fun _ h => h 0)
  let δ := s * κ
  let ρ := 2 * environmentLaw ν {ω | noDropQuenched ℓ 0 ω ≤ 2 * (s : ℝ≥0∞)}
  have hδ : 0 < δ := mul_pos hs hκ
  have hδle : δ < 1 := by
    have hle : δ ≤ 1 / 4 := (mul_le_mul' hsle hκle).trans (by norm_num)
    exact hle.trans_lt (by norm_num)
  have hρ : ρ < 1 := by
    apply lt_of_lt_of_le (b := (2 : ℝ≥0∞) * (1 / 4))
    · exact ENNReal.mul_lt_mul_right (by norm_num) (by norm_num) hsμ
    · rw [one_div, ENNReal.mul_inv_le_iff (by norm_num) (by norm_num)]
      norm_num
  refine ⟨δ, ρ, hδ, hδle, hρ, ?_⟩
  intro j
  induction j with
  | zero => rw [pow_zero]; exact prob_le_one
  | succ j ih =>
    have hrec := noDrop_small_recursive ν ℓ e he htrans
      (hκae.mono fun _ h x => h x e)
      (t := δ ^ (j + 1)) (r := δ ^ (j + 1 + 1)) (s := s)
      (pow_lt_one₀ hδ.le hδle (by omega))
      (by rw [pow_succ]; exact mul_le_of_le_one_right zero_le hδle.le) hs
      (by rw [pow_succ]; dsimp [δ]; ring_nf; rfl)
    calc
      _ ≤ ρ * environmentLaw ν {ω | noDropQuenched ℓ 0 ω < ((δ ^ (j + 1) : ℝ≥0) : ℝ≥0∞)} := hrec
      _ ≤ ρ * ρ ^ j := mul_le_mul' le_rfl ih
      _ = ρ ^ (j + 1) := (pow_succ' ρ j).symm

lemma exists_inverse_geometric_ratio {δ : ℝ≥0} (hδ : 0 < δ)
    {ρ : ℝ≥0∞} (hρ : ρ < 1) :
    ∃ lam : ℝ, 0 < lam ∧ ρ * ((δ ^ (-lam) : ℝ≥0) : ℝ≥0∞) < 1 := by
  have hp : ContinuousAt (fun t : ℝ => (δ, -t)) 0 :=
    ContinuousAt.prodMk (f := fun _ : ℝ => δ) (g := fun t : ℝ => -t)
      continuousAt_const continuousAt_neg
  have hc0 : ContinuousAt (fun p : ℝ≥0 × ℝ => p.1 ^ p.2) (δ, -(0 : ℝ)) :=
    NNReal.continuousAt_rpow (Or.inl hδ.ne')
  have hh0 := hc0.comp (f := fun t : ℝ => (δ, -t)) hp
  change ContinuousAt (fun t : ℝ => δ ^ (-t)) 0 at hh0
  have hc : ContinuousAt (fun t : ℝ => ρ.toNNReal * δ ^ (-t)) 0 :=
    continuousAt_const.mul hh0
  have hr : ρ.toNNReal < 1 := by
    exact_mod_cast (ENNReal.toNNReal_lt_toNNReal (ne_top_of_lt hρ) ENNReal.one_ne_top).mpr hρ
  have hh := hc.eventually (eventually_lt_nhds (show ρ.toNNReal * δ ^ (-(0 : ℝ)) < 1 by simpa using hr))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨ε / 2, by positivity, ?_⟩
  have hh' := he (y := ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; exact half_lt_self hε)
  rw [← ENNReal.coe_toNNReal (ne_top_of_lt hρ), ← ENNReal.coe_mul]
  exact_mod_cast hh'

lemma inverse_power_le_series {δ : ℝ≥0} (hδ : 0 < δ) (hδ1 : δ < 1)
    {lam : ℝ} (hlam : 0 < lam) {x : ℝ≥0} (hx : 0 < x) :
    ((x ^ (-lam) : ℝ≥0) : ℝ≥0∞) ≤ ((δ ^ (-lam) : ℝ≥0) : ℝ≥0∞) +
      ∑' j : ℕ, (Set.Iio (δ ^ (j + 1))).indicator
        (fun _ : ℝ≥0 => ((δ ^ (-lam) : ℝ≥0) : ℝ≥0∞) ^ (j + 2)) x := by
  classical
  have hex : ∃ n : ℕ, δ ^ (n + 1) ≤ x := by
    obtain ⟨n, hn⟩ := ((NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hδ1).eventually
      (eventually_lt_nhds hx)).exists
    exact ⟨n, (pow_le_pow_right_of_le_one' hδ1.le (Nat.le_succ n)).trans hn.le⟩
  let n := Nat.find hex
  have hnx : δ ^ (n + 1) ≤ x := Nat.find_spec hex
  have hbound : ((x ^ (-lam) : ℝ≥0) : ℝ≥0∞) ≤ ((δ ^ (-lam) : ℝ≥0) : ℝ≥0∞) ^ (n + 1) := by
    have hh := NNReal.rpow_le_rpow_of_nonpos (pow_pos hδ _) hnx (neg_nonpos.mpr hlam.le)
    have heq : (δ ^ (n + 1)) ^ (-lam) = (δ ^ (-lam)) ^ (n + 1) := by
      rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, mul_comm, NNReal.rpow_mul,
        NNReal.rpow_natCast]
    rw [heq] at hh
    exact_mod_cast hh
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simpa [hn] using hbound.trans (le_add_right le_rfl)
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    have hlt : x < δ ^ (j + 1) := lt_of_not_ge (Nat.find_min hex (show j < n by omega))
    have hs := ENNReal.le_tsum (f := fun k : ℕ => (Set.Iio (δ ^ (k + 1))).indicator
      (fun _ : ℝ≥0 => ((δ ^ (-lam) : ℝ≥0) : ℝ≥0∞) ^ (k + 2)) x) j
    rw [Set.indicator_of_mem (show x ∈ Set.Iio (δ ^ (j + 1)) from hlt)] at hs
    exact hbound.trans (by simpa [hj, add_assoc] using hs.trans (le_add_left le_rfl))

end DirectionalTransience
end
end

end OAI
