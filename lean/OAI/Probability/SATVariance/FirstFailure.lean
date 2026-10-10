import OAI.Probability.SATVariance.ClauseCombinatorics

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma prefixSAT_zero {n k : ℕ} (ω : Stream n k) : PrefixSAT ω 0 :=
  ⟨fun _ => false, fun _ hi => False.elim (Nat.not_lt_zero _ hi)⟩

lemma prefixSAT_mono {n k : ℕ} {ω : Stream n k} {m t : ℕ}
    (h : m ≤ t) : PrefixSAT ω t → PrefixSAT ω m := by
  rintro ⟨a, ha⟩
  exact ⟨a, fun i hi => ha i (hi.trans_le h)⟩

lemma lt_firstFailure_iff {n k : ℕ} (ω : Stream n k) (m : ℕ) :
    (m : ℕ∞) < firstFailure ω ↔ PrefixSAT ω m := by
  constructor
  · intro hm
    by_contra hn
    exact (not_le_of_gt hm) (sInf_le ⟨m, hn, rfl⟩)
  · intro hm
    have hle : ((m + 1 : ℕ) : ℕ∞) ≤ firstFailure ω := by
      apply le_sInf
      rintro _ ⟨t, ht, rfl⟩
      have hmt : m < t := by
        by_contra h
        exact ht (prefixSAT_mono (Nat.le_of_not_gt h) hm)
      exact ENat.natCast_le_natCast.mpr (Nat.succ_le_of_lt hmt)
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hle

lemma firstFailure_le_iff {n k : ℕ} (ω : Stream n k) (m : ℕ) :
    firstFailure ω ≤ m ↔ ¬ PrefixSAT ω m := by
  rw [← not_lt, lt_firstFailure_iff]

lemma firstFailure_pos {n k : ℕ} (ω : Stream n k) : 0 < firstFailure ω := by
  exact (lt_firstFailure_iff ω 0).mpr (prefixSAT_zero ω)

lemma assignment_survival {n k : ℕ} (hkn : k ≤ n) (a : Assignment n) (m : ℕ) :
    streamLaw n k {ω | ∀ i < m, Satisfies (ω i) a} =
      (1 - ((2 : ℝ≥0∞) ^ k)⁻¹) ^ m := by
  let := clauseLaw_probability n k hkn
  have he : {ω : Stream n k | ∀ i < m, Satisfies (ω i) a} =
      Set.pi (Finset.range m) (fun _ => {c : Clause n k | Satisfies c a}) := by
    ext ω
    simp
  rw [he, streamLaw, Measure.infinitePi_pi]
  · simp [clauseLaw_satisfies hkn]
  · intro i _
    exact (Set.toFinite _).measurableSet

lemma first_moment_tail {n k : ℕ} (hkn : k ≤ n) (m : ℕ) :
    streamLaw n k {ω | (m : ℕ∞) < firstFailure ω} ≤
      (2 : ℝ≥0∞) ^ n * (1 - ((2 : ℝ≥0∞) ^ k)⁻¹) ^ m := by
  have he : {ω : Stream n k | (m : ℕ∞) < firstFailure ω} =
      ⋃ a : Assignment n, {ω | ∀ i < m, Satisfies (ω i) a} := by
    ext ω
    simp [lt_firstFailure_iff, PrefixSAT]
  rw [he]
  calc
    _ ≤ ∑ a : Assignment n, streamLaw n k {ω | ∀ i < m, Satisfies (ω i) a} :=
      measure_iUnion_fintype_le _ _
    _ = _ := by simp [assignment_survival hkn]

lemma measurableSet_prefixSAT (n k m : ℕ) :
    MeasurableSet {ω : Stream n k | PrefixSAT ω m} := by
  simp only [PrefixSAT, Set.ofPred_exists, Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  exact (Set.toFinite {c : Clause n k | Satisfies c a}).measurableSet.preimage
    (measurable_pi_apply i)

lemma firstFailure_eq_succ_iff {n k : ℕ} (ω : Stream n k) (m : ℕ) :
    firstFailure ω = (m + 1 : ℕ) ↔ PrefixSAT ω m ∧ ¬ PrefixSAT ω (m + 1) := by
  rw [← lt_firstFailure_iff, ← firstFailure_le_iff]
  constructor
  · intro h
    rw [h]
    exact ⟨ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self m), le_rfl⟩
  · rintro ⟨h₁, h₂⟩
    apply le_antisymm h₂
    exact (ENat.natCast_add_one_le_iff).mpr h₁

lemma measurable_firstFailure (n k : ℕ) :
    Measurable (firstFailure : Stream n k → ℕ∞) := by
  apply ENat.measurable_iff.mpr
  intro m
  cases m with
  | zero =>
    have he : (firstFailure : Stream n k → ℕ∞) ⁻¹' {0} = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact ne_of_gt (firstFailure_pos ω)
    simpa only [Nat.cast_zero, he] using MeasurableSet.empty
  | succ m =>
    have he : (firstFailure : Stream n k → ℕ∞) ⁻¹' {↑(m + 1)} =
        {ω | PrefixSAT ω m} ∩ {ω | PrefixSAT ω (m + 1)}ᶜ := by
      ext ω
      exact firstFailure_eq_succ_iff ω m
    rw [he]
    exact (measurableSet_prefixSAT n k m).inter (measurableSet_prefixSAT n k (m+1)).compl

lemma measurable_H (n k : ℕ) : Measurable (H : Stream n k → ℝ) :=
  (measurable_of_countable (fun x : ℕ∞ => (x.toNat : ℝ))).comp (measurable_firstFailure n k)

lemma measurable_T (n k : ℕ) (B : ℝ) : Measurable (T B : Stream n k → ℝ) :=
  (measurable_of_countable (fun x : ℕ∞ => ((min x (cap n B : ℕ∞)).toNat : ℝ))).comp
    (measurable_firstFailure n k)

lemma survival_rate_lt_one (k : ℕ) : (1 - ((2 : ℝ≥0∞) ^ k)⁻¹) < 1 := by
  apply ENNReal.sub_lt_self (by simp) (by simp)
  exact ne_of_gt (ENNReal.inv_pos.mpr (by finiteness))

lemma firstFailure_finite_ae {n k : ℕ} (hkn : k ≤ n) :
    ∀ᵐ ω ∂streamLaw n k, firstFailure ω < ⊤ := by
  have ht : Filter.Tendsto (fun m : ℕ =>
      (2 : ℝ≥0∞) ^ n * (1 - ((2 : ℝ≥0∞) ^ k)⁻¹) ^ m) Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (survival_rate_lt_one k))
      (Or.inr (by finiteness : (2 : ℝ≥0∞) ^ n ≠ ⊤))
  rw [ae_iff]
  apply le_antisymm _ bot_le
  apply ge_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro m
  apply le_trans (measure_mono ?_) (first_moment_tail hkn m)
  intro ω hω
  have htop : firstFailure ω = ⊤ := top_unique (not_lt.mp hω)
  change (m : ℕ∞) < firstFailure ω
  rw [htop]
  exact ENat.natCast_lt_top m

lemma T_nonneg {n k : ℕ} (B : ℝ) (ω : Stream n k) : 0 ≤ T B ω := by
  unfold T
  positivity

lemma T_le_cap {n k : ℕ} (B : ℝ) (ω : Stream n k) : T B ω ≤ cap n B := by
  unfold T
  exact_mod_cast ENat.toNat_le_of_le_natCast (min_le_right (firstFailure ω) (cap n B : ℕ∞))

lemma T_memLp {n k : ℕ} (hkn : k ≤ n) (B : ℝ) (p : ℝ≥0∞) :
    MemLp (T B : Stream n k → ℝ) p (streamLaw n k) := by
  let := streamLaw_probability n k hkn
  apply MemLp.of_bound (measurable_T n k B).aestronglyMeasurable (cap n B)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (T_nonneg B ω)]
  exact T_le_cap B ω

end RandomKSAT

end

end OAI
