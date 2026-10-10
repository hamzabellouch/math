import OAI.GroupTheory.PolycyclicRecognition.Analysis.SublinearScaleOffsets
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceScaleExtraction

namespace OAI

/-! # Passing from adjacent-scale comparisons to uniform stabilization -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- Nearby-scale equality propagates along a finite geometric chain. -/
theorem scale_label_eq_of_nearby
    {P L : Type*} (label : P → ℝ → L) {q R : ℝ} (hq : 1 < q) (hR : 0 < R)
    (hnear : ∀ p r t, R ≤ r → r ≤ t → t ≤ q * r → label p r = label p t) :
    ∀ p r, R ≤ r → label p r = label p R := by
  intro p r hr
  have hpow (n : ℕ) : R ≤ q ^ n * R := by
    simpa using mul_le_mul_of_nonneg_right (one_le_pow₀ hq.le) hR.le
  have hchain (n : ℕ) : label p (q ^ n * R) = label p R := by
    induction n with
    | zero => simp
    | succ n ih =>
        apply Eq.trans _ ih
        symm
        apply hnear p _ _ (hpow n)
        · rw [pow_succ]
          simpa only [one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using
            mul_le_mul_of_nonneg_right hq.le
              (mul_nonneg (pow_nonneg (zero_lt_one.trans hq).le n) hR.le)
        · rw [pow_succ]
          ring_nf
          exact le_rfl
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near ((one_le_div hR).mpr hr) hq
  have hlow : q ^ n * R ≤ r := (le_div_iff₀ hR).mp hn
  have hupp : r ≤ q * (q ^ n * R) := by
    have hh := (div_lt_iff₀ hR).mp hn'
    rw [pow_succ] at hh
    nlinarith
  exact (hnear p _ _ (hpow n) hlow hupp).symm.trans (hchain n)

/-- Sequential comparison at arbitrary increasing source and target scales
is enough for the uniform estimate used in the geometric telescoping step. -/
theorem uniform_nearby_bound_of_strict_sequences
    {P : Type*} (err : P → ℝ → ℝ → ℝ) (q : ℝ)
    (hseq : ∀ (p : ℕ → P) (r t : ℕ → ℝ),
      Tendsto r atTop atTop → StrictMono r → StrictMono t →
      (∀ n, 1 ≤ r n) → (∀ n, r n ≤ t n) → (∀ n, t n ≤ q * r n) →
      Tendsto (fun n => err (p n) (r n) (t n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ p r t, R ≤ r → r ≤ t → t ≤ q * r → err p r t ≤ ε := by
  classical
  intro ε hε
  by_contra h
  push Not at h
  have hex (n : ℕ) := h (max 1 (n : ℝ)) (le_max_left _ _)
  choose p r t hr hrt ht he using hex
  have hr1 n : 1 ≤ r n := (le_max_left _ _).trans (hr n)
  have hrgrow : Tendsto r atTop atTop := tendsto_atTop_mono
    (fun n => (le_max_right _ _).trans (hr n)) tendsto_natCast_atTop_atTop
  obtain ⟨u, hu, hru, _⟩ := exists_strictMono_scale_subsequence r hrgrow
  have htgrow : Tendsto (t ∘ u) atTop atTop :=
    (tendsto_atTop_mono hrt hrgrow).comp hu.tendsto_atTop
  obtain ⟨v, hv, htv, _⟩ := exists_strictMono_scale_subsequence (t ∘ u) htgrow
  have hh := hseq (p ∘ u ∘ v) (r ∘ u ∘ v) (t ∘ u ∘ v)
    (hrgrow.comp (hu.comp hv).tendsto_atTop) (hru.comp hv) htv
    (fun n => hr1 (u (v n))) (fun n => hrt (u (v n))) (fun n => ht (u (v n)))
  obtain ⟨n, hn⟩ := (hh.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (he (u (v n))).le) hn

/-- Eventual equality along every scale sequence yields a single uniform
threshold for all maps and basepoints. -/
theorem uniform_nearby_labels_of_strict_sequences
    {P L : Type*} (label : P → ℝ → L) (q : ℝ)
    (hseq : ∀ (p : ℕ → P) (r t : ℕ → ℝ),
      Tendsto r atTop atTop → StrictMono r → StrictMono t →
      (∀ n, 1 ≤ r n) → (∀ n, r n ≤ t n) → (∀ n, t n ≤ q * r n) →
      ∀ᶠ n in atTop, label (p n) (r n) = label (p n) (t n)) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ p r t, R ≤ r → r ≤ t → t ≤ q * r →
      label p r = label p t := by
  classical
  let err := fun p r t => if label p r = label p t then (0 : ℝ) else 1
  have he := uniform_nearby_bound_of_strict_sequences err q (by
    intro p r t hrg hr ht hr1 hrt htq
    apply tendsto_const_nhds.congr'
    filter_upwards [hseq p r t hrg hr ht hr1 hrt htq] with n hn
    simp only [err, hn, ite_true]) (1 / 2) (by norm_num)
  obtain ⟨R, hR, hb⟩ := he
  refine ⟨R, hR, ?_⟩
  intro p r t hr hrt htq
  have hh := hb p r t hr hrt htq
  by_contra hne
  simp [err, hne] at hh
  norm_num at hh

theorem physical_offset_increment_eq
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {r : ℝ} (hr : 0 < r) (t : ℝ) (b c : W) :
    ‖r • b - t • c‖ = r * dist b ((t / r) • c) := by
  have he : r * (t / r) = t := by field_simp
  calc
    _ = ‖r • (b - (t / r) • c)‖ := by rw [smul_sub, smul_smul, he]
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, dist_eq_norm]

/-- The normalized mean offsets vanish uniformly once their comparisons
at nearby scales vanish uniformly. -/
theorem uniform_zero_of_normalized_scale_increments
    {P W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (b : P → ℝ → W) {Q C : ℝ} (hQ : 1 < Q)
    (hbound : ∀ p r, 1 ≤ r → ‖b p r‖ ≤ C)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ p r t, R ≤ r → r ≤ t → t ≤ Q * r →
        dist (b p r) ((t / r) • b p t) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ p r, R ≤ r → ‖b p r‖ ≤ ε := by
  let s := fun p r => r • b p r
  have hQ0 : 0 < Q := zero_lt_one.trans hQ
  have hq : 0 < Q⁻¹ := inv_pos.mpr hQ0
  have hq1 : Q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hQ
  have hsbound p r (hr : 1 ≤ r) : ‖s p r‖ ≤ C * r := by
    change ‖r • b p r‖ ≤ C * r
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans_le hr), mul_comm C]
    exact mul_le_mul_of_nonneg_left (hbound p r hr) (zero_le_one.trans hr)
  have hinc : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧
      ∀ p r, R ≤ r → ‖s p r - s p (Q⁻¹ * r)‖ ≤ ε * r := by
    intro ε hε
    obtain ⟨R, hR, hRnear⟩ := hnear ε hε
    refine ⟨max 1 (Q * R), le_max_left _ _, ?_⟩
    intro p r hr
    have hr0 : 0 < r := zero_lt_one.trans_le ((le_max_left _ _).trans hr)
    have hqr0 : 0 < Q⁻¹ * r := mul_pos hq hr0
    have hRqr : R ≤ Q⁻¹ * r := by
      have hh := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hr) hq.le
      simpa only [← mul_assoc, inv_mul_cancel₀ hQ0.ne', one_mul] using hh
    have hqrr : Q⁻¹ * r ≤ r := by nlinarith [mul_nonneg (sub_nonneg.mpr hq1.le) hr0.le]
    have hqr : Q * (Q⁻¹ * r) = r := by rw [← mul_assoc, mul_inv_cancel₀ hQ0.ne', one_mul]
    have hh := hRnear p (Q⁻¹ * r) r hRqr hqrr hqr.symm.le
    calc
      ‖s p r - s p (Q⁻¹ * r)‖ = ‖s p (Q⁻¹ * r) - s p r‖ := norm_sub_rev _ _
      _ = (Q⁻¹ * r) * dist (b p (Q⁻¹ * r)) ((r / (Q⁻¹ * r)) • b p r) :=
        physical_offset_increment_eq hqr0 r _ _
      _ ≤ (Q⁻¹ * r) * ε := mul_le_mul_of_nonneg_left hh hqr0.le
      _ ≤ ε * r := by nlinarith
  intro ε hε
  obtain ⟨R, hR, hRs⟩ := uniform_sublinear_of_contractive_increments s hq hq1 hsbound hinc ε hε
  refine ⟨R, hR, ?_⟩
  intro p r hr
  have hh := hRs p r hr
  change ‖r • b p r‖ ≤ ε * r at hh
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans_le (hR.trans hr))] at hh
  exact (mul_le_mul_iff_right₀ (zero_lt_one.trans_le (hR.trans hr))).mp (by
    simpa only [mul_comm] using hh)

/-- The two conclusions needed from adjacent-scale comparison: a uniform
stable label and a uniformly vanishing normalized offset. -/
theorem uniform_scale_stabilization_of_sequences
    {P L W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (label : P → ℝ → L) (b : P → ℝ → W) {Q C : ℝ} (hQ : 1 < Q)
    (hbound : ∀ p r, 1 ≤ r → ‖b p r‖ ≤ C)
    (hseq : ∀ (p : ℕ → P) (r t : ℕ → ℝ),
      Tendsto r atTop atTop → StrictMono r → StrictMono t →
      (∀ n, 1 ≤ r n) → (∀ n, r n ≤ t n) → (∀ n, t n ≤ Q * r n) →
      (∀ᶠ n in atTop, label (p n) (r n) = label (p n) (t n)) ∧
      Tendsto (fun n => dist (b (p n) (r n)) ((t n / r n) • b (p n) (t n)))
        atTop (𝓝 0)) :
    (∃ R : ℝ, 1 ≤ R ∧ ∀ p r, R ≤ r → label p r = label p R) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ p r, R ≤ r → ‖b p r‖ ≤ ε) := by
  obtain ⟨R, hR, hlabels⟩ := uniform_nearby_labels_of_strict_sequences label Q
    (fun p r t hrg hr ht hr1 hrt htQ => (hseq p r t hrg hr ht hr1 hrt htQ).1)
  refine ⟨⟨R, hR, scale_label_eq_of_nearby label hQ (zero_lt_one.trans_le hR) hlabels⟩, ?_⟩
  apply uniform_zero_of_normalized_scale_increments b hQ hbound
  exact uniform_nearby_bound_of_strict_sequences
    (fun p r t => dist (b p r) ((t / r) • b p t)) Q
    (fun p r t hrg hr ht hr1 hrt htQ => (hseq p r t hrg hr ht hr1 hrt htQ).2)

end PolycyclicRecognition

end OAI
