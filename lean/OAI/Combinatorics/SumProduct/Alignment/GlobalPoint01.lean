import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.PointLaw02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
noncomputable section
end

 

section
 

 

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace GlobalPointLaw

 
def cell (N d r : ℕ) (a b : ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun k => a ≤ (k.val : ℝ) / N ∧ (k.val : ℝ) / N < b ∧ k.val % d = r

@[simp] lemma mem_cell {N d r : ℕ} {a b : ℝ} {k : Fin N} :
    k ∈ cell N d r a b ↔
      a ≤ (k.val : ℝ) / N ∧ (k.val : ℝ) / N < b ∧ k.val % d = r := by
  simp [cell]

lemma normalized_mem {N : ℕ} (k : Fin N) :
    (k.val : ℝ) / N ∈ Set.Ico (0 : ℝ) 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt k.isLt)
  constructor
  · positivity
  · exact (div_lt_one hN).mpr (by exact_mod_cast k.isLt)

 
lemma exists_unique_partition_cell {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    ∃! i : Fin n, (i.val : ℝ) / n ≤ x ∧ x < ((i.val : ℝ) + 1) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx : 0 ≤ x * n := mul_nonneg hx.1 hnR.le
  have hlt : ⌊x * (n : ℝ)⌋₊ < n := by
    apply (Nat.floor_lt hnx).mpr
    simpa using (mul_lt_mul_of_pos_right hx.2 hnR)
  let i : Fin n := ⟨⌊x * (n : ℝ)⌋₊, hlt⟩
  refine ⟨i, ⟨?_, ?_⟩, ?_⟩
  · exact (div_le_iff₀ hnR).mpr (Nat.floor_le hnx)
  · exact (lt_div_iff₀ hnR).mpr (Nat.lt_floor_add_one (x * (n : ℝ)))
  · intro j hj
    apply Fin.ext
    change j.val = ⌊x * (n : ℝ)⌋₊
    symm
    apply (Nat.floor_eq_iff hnx).mpr
    exact ⟨(div_le_iff₀ hnR).mp hj.1, (lt_div_iff₀ hnR).mp hj.2⟩

 
lemma sum_cells {A : Type*} [AddCommMonoid A] {n d N : ℕ}
    (hn : 0 < n) (hd : 0 < d) (f : Fin N → A) :
    (∑ i : Fin n, ∑ r : Fin d,
      ∑ k ∈ cell N d r.val ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n), f k) =
      ∑ k : Fin N, f k := by
  simp only [cell, Finset.sum_filter]
  calc
    _ = ∑ i : Fin n, ∑ k : Fin N, ∑ r : Fin d,
        if (i.val : ℝ) / n ≤ (k.val : ℝ) / N ∧
          (k.val : ℝ) / N < ((i.val : ℝ) + 1) / n ∧ k.val % d = r.val
        then f k else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ k : Fin N, ∑ i : Fin n, ∑ r : Fin d,
        if (i.val : ℝ) / n ≤ (k.val : ℝ) / N ∧
          (k.val : ℝ) / N < ((i.val : ℝ) + 1) / n ∧ k.val % d = r.val
        then f k else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      obtain ⟨j, hj, hjunique⟩ := exists_unique_partition_cell hn (normalized_mem k)
      let r₀ : Fin d := ⟨k.val % d, Nat.mod_lt _ hd⟩
      have hiff (i : Fin n) (r : Fin d) :
          ((i.val : ℝ) / n ≤ (k.val : ℝ) / N ∧
            (k.val : ℝ) / N < ((i.val : ℝ) + 1) / n ∧ k.val % d = r.val) ↔
            i = j ∧ r = r₀ := by
        constructor
        · intro h
          exact ⟨hjunique i ⟨h.1, h.2.1⟩, Fin.ext h.2.2.symm⟩
        · rintro ⟨rfl, rfl⟩
          exact ⟨hj.1, hj.2, rfl⟩
      simp_rw [hiff, ite_and]
      simp

 
def riemann (n : ℕ) (f : ℝ → ℂ) : ℂ :=
  ∑ i : Fin n, (1 / (n : ℝ)) • f ((i.val : ℝ) / n)

lemma partition_endpoints {n : ℕ} (hn : 0 < n) (i : Fin n) :
    0 ≤ (i.val : ℝ) / n ∧
    (i.val : ℝ) / n ≤ ((i.val : ℝ) + 1) / n ∧
    ((i.val : ℝ) + 1) / n ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨by positivity, div_le_div_of_nonneg_right (by linarith) hnR.le, ?_⟩
  apply (div_le_one hnR).mpr
  exact_mod_cast i.isLt

 

lemma riemann_error {n : ℕ} (hn : 0 < n) (f : ℝ → ℂ) (hf : Continuous f)
    {ε : ℝ} (_hε : 0 ≤ ε)
    (hosc : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |x - y| ≤ 1 / (n : ℝ) → ‖f x - f y‖ ≤ ε) :
    ‖riemann n f - ∫ x in (0 : ℝ)..1, f x‖ ≤ ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (∑ i : Fin n,
        ∫ x in (i.val : ℝ) / n..((i.val : ℝ) + 1) / n, f x) =
        ∫ x in (0 : ℝ)..1, f x := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      ∫ x in (k : ℝ) / n..((k : ℝ) + 1) / n, f x) n]
    have ht := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) / n) (f := f)
      (n := n) (μ := volume) (fun k hk => hf.intervalIntegrable _ _)
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div,
      div_self hnR.ne'] using ht
  have hterm (i : Fin n) :
      ‖(1 / (n : ℝ)) • f ((i.val : ℝ) / n) -
        ∫ x in (i.val : ℝ) / n..((i.val : ℝ) + 1) / n, f x‖ ≤ ε / n := by
    obtain ⟨hleft, hle, hright⟩ := partition_endpoints hn i
    have hlen : ((i.val : ℝ) + 1) / n - (i.val : ℝ) / n = 1 / n := by ring
    have hc : (1 / (n : ℝ)) • f ((i.val : ℝ) / n) =
        ∫ _x in (i.val : ℝ) / n..((i.val : ℝ) + 1) / n,
          f ((i.val : ℝ) / n) := by
      rw [intervalIntegral.integral_const, hlen]
    rw [hc, ← intervalIntegral.integral_sub
      (intervalIntegrable_const) (hf.intervalIntegrable _ _)]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (C := ε)
      (a := (i.val : ℝ) / n) (b := ((i.val : ℝ) + 1) / n)
      (f := fun x => f ((i.val : ℝ) / n) - f x) (by
        intro x hx
        rw [Set.uIoc_of_le hle] at hx
        apply hosc _ ⟨hleft, hle.trans hright⟩ _ ⟨hleft.trans hx.1.le, hx.2.trans hright⟩
        rw [abs_of_nonpos (sub_nonpos.mpr hx.1.le)]
        linarith only [hx.2, hlen])
    rw [hlen, abs_of_pos (one_div_pos.mpr hnR)] at hb
    simpa only [div_eq_mul_inv, one_mul] using hb
  rw [← hsum, riemann, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin n, ‖(1 / (n : ℝ)) • f ((i.val : ℝ) / n) -
        ∫ x in (i.val : ℝ) / n..((i.val : ℝ) + 1) / n, f x‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ε / (n : ℝ) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = ε := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

 
lemma prefix_count_error {d r : ℕ} (hd : 0 < d) (hr : r < d) (M : ℕ) :
    |(Nat.count (fun k => k % d = r) M : ℝ) - (M : ℝ) / d| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he : Nat.count (fun k => k % d = r) M =
      M / d + if r < M % d then 1 else 0 := by
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hr] using Nat.count_modEq_card M hd r
  have hmod : ((M % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt M hd
  have hmod0 : (0 : ℝ) ≤ ((M % d : ℕ) : ℝ) := by positivity
  have hdiv : ((M / d : ℕ) : ℝ) * d + ((M % d : ℕ) : ℝ) = M := by
    exact_mod_cast (by simpa only [Nat.mul_comm] using Nat.div_add_mod M d : M / d * d + M % d = M)
  have hquot : (M : ℝ) / d = ((M / d : ℕ) : ℝ) + ((M % d : ℕ) : ℝ) / d := by
    apply (div_eq_iff hdR.ne').mpr
    field_simp
    nlinarith [hdiv]
  have hlo := div_nonneg hmod0 hdR.le
  have hhi : ((M % d : ℕ) : ℝ) / d < 1 := (div_lt_one hdR).mpr hmod
  rw [he, hquot, abs_le]
  split_ifs <;> push_cast <;> constructor <;> linarith

lemma interval_filter_card (A B : ℕ) (hAB : A ≤ B) (p : ℕ → Prop) [DecidablePred p] :
    ((Finset.Ico A B).filter p).card = Nat.count p B - Nat.count p A := by
  have he : (Finset.Ico A B).filter p =
      (Finset.range B).filter p \ (Finset.range A).filter p := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_range]
    by_cases hp : p k
    · simp only [hp, and_true]; omega
    · simp only [hp, and_false, not_false_eq_true, false_and]
  have hsub : (Finset.range A).filter p ⊆ (Finset.range B).filter p := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨hk.1.trans_le hAB, hk.2⟩
  rw [he, Finset.card_sdiff_of_subset hsub, Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]

 
lemma cell_card {N d r : ℕ} (hN : 0 < N) {a b : ℝ}
    (_ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (cell N d r a b).card =
      Nat.count (fun k => k % d = r) ⌈b * N⌉₊ -
        Nat.count (fun k => k % d = r) ⌈a * N⌉₊ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← interval_filter_card ⌈a * N⌉₊ ⌈b * N⌉₊
    (Nat.ceil_mono (mul_le_mul_of_nonneg_right hab hN'.le))]
  apply Finset.card_bij (fun k _ => k.val)
  · intro k hk
    have hk' := mem_cell.mp hk
    simp only [Finset.mem_filter, Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil]
    exact ⟨⟨(le_div_iff₀ hN').mp hk'.1, (div_lt_iff₀ hN').mp hk'.2.1⟩, hk'.2.2⟩
  · intro k hk k' hk' he
    exact Fin.ext he
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil] at hk
    have hkN : k < N := by
      have := hk.1.2.trans_le (mul_le_of_le_one_left hN'.le hb)
      exact_mod_cast this
    refine ⟨⟨k, hkN⟩, ?_, rfl⟩
    apply mem_cell.mpr
    exact ⟨(le_div_iff₀ hN').mpr hk.1.1, (div_lt_iff₀ hN').mpr hk.1.2, hk.2⟩

 
lemma prefix_density {d r : ℕ} (hd : 0 < d) (hr : r < d) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun N : ℕ =>
      (Nat.count (fun k => k % d = r) ⌈β * N⌉₊ : ℝ) / N) atTop (𝓝 (β / d)) := by
  have hmain : Tendsto (fun N : ℕ => ((⌈β * N⌉₊ : ℝ) / d) / N)
      atTop (𝓝 (β / d)) := by
    convert (((tendsto_nat_ceil_mul_div_atTop hβ).comp
      tendsto_natCast_atTop_atTop).div_const (d : ℝ)) using 1
    ext N
    simp only [Function.comp_apply]
    ring
  have hz : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using hmain.sub hz)
    (by simpa only [add_zero] using hmain.add hz)
  · exact Filter.Eventually.of_forall (fun N => by
      have hlo := (abs_le.mp (prefix_count_error hd hr ⌈β * N⌉₊)).1
      have h := div_le_div_of_nonneg_right hlo (show (0 : ℝ) ≤ N by positivity)
      rw [sub_div] at h
      simp only [neg_div] at h
      linarith)
  · exact Filter.Eventually.of_forall (fun N => by
      have hhi := (abs_le.mp (prefix_count_error hd hr ⌈β * N⌉₊)).2
      have h := div_le_div_of_nonneg_right hhi (show (0 : ℝ) ≤ N by positivity)
      rw [sub_div] at h
      linarith)

 
lemma cell_density {d r : ℕ} (hd : 0 < d) (hr : r < d) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => ((cell N d r a b).card : ℝ) / N)
      atTop (𝓝 ((b - a) / d)) := by
  have hlim := (prefix_density hd hr (ha.trans hab)).sub (prefix_density hd hr ha)
  rw [← sub_div] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [cell_card hN ha hab hb, Nat.cast_sub, sub_div]
  exact Nat.count_monotone _ (Nat.ceil_mono (mul_le_mul_of_nonneg_right hab (by positivity)))

section Tests
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]

lemma test_integrable (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℂ)) :
    Integrable f μ :=
  Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall f.norm_coe_le_norm)

 

lemma integral_lipschitz (μ : Measure X) [IsProbabilityMeasure μ] :
    LipschitzWith 1 (fun f : C(X, ℂ) => ∫ x, f x ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [← integral_sub (test_integrable μ f) (test_integrable μ g)]
  have hb := norm_integral_le_of_norm_le_const (μ := μ) (C := ‖f - g‖)
    (Filter.Eventually.of_forall fun x => (f - g).norm_coe_le_norm x)
  simpa using hb

lemma continuous_integral (μ : Measure X) [IsProbabilityMeasure μ]
    (Φ : ℝ → C(X, ℂ)) (hΦ : Continuous Φ) :
    Continuous (fun β => ∫ x, Φ β x ∂μ) :=
  (integral_lipschitz μ).continuous.comp hΦ

 
def empirical {N : ℕ} (q : Fin N → X) (Φ : ℝ → C(X, ℂ)) : ℂ :=
  (1 / (N : ℝ)) • ∑ k : Fin N, Φ ((k.val : ℝ) / N) (q k)

 
def frozen (n d : ℕ) {N : ℕ} (q : Fin N → X) (Φ : ℝ → C(X, ℂ)) : ℂ :=
  (1 / (N : ℝ)) • ∑ i : Fin n, ∑ r : Fin d,
    ∑ k ∈ cell N d r.val ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n),
      Φ ((i.val : ℝ) / n) (q k)

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
lemma empirical_frozen_error {n d N : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hN : 0 < N) (q : Fin N → X) (Φ : ℝ → C(X, ℂ)) {ε : ℝ}
    (hosc : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |x - y| ≤ 1 / (n : ℝ) → ‖Φ x - Φ y‖ ≤ ε) :
    ‖empirical q Φ - frozen n d q Φ‖ ≤ ε := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := sum_cells hn hd (fun k : Fin N => Φ ((k.val : ℝ) / N) (q k))
  rw [empirical, frozen, ← hsum, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hN')]
  simp only [← Finset.sum_sub_distrib]
  have hterm (i : Fin n) (r : Fin d)
      (k : Fin N) (hk : k ∈ cell N d r.val
        ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)) :
      ‖Φ ((k.val : ℝ) / N) (q k) - Φ ((i.val : ℝ) / n) (q k)‖ ≤ ε := by
    obtain ⟨hleft, hle, hright⟩ := partition_endpoints hn i
    have hk' := mem_cell.mp hk
    have hk01 := normalized_mem k
    apply ((Φ ((k.val : ℝ) / N) - Φ ((i.val : ℝ) / n)).norm_coe_le_norm (q k)).trans
    apply hosc _ ⟨hk01.1, hk01.2.le⟩ _ ⟨hleft, hle.trans hright⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hk'.1)]
    have hlen : ((i.val : ℝ) + 1) / n - (i.val : ℝ) / n = 1 / n := by ring
    linarith only [hk'.2.1, hlen]
  calc
    _ ≤ (1 / (N : ℝ)) * ∑ i : Fin n, ∑ r : Fin d,
        ∑ k ∈ cell N d r.val ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n), ε := by
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hN'.le)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r hr
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun k hk => hterm i r k hk)
    _ = ε := by
      rw [sum_cells hn hd (fun _k : Fin N => ε)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

 
def betaMixture {d : ℕ} (μ : Fin d → Measure X) (Φ : ℝ → C(X, ℂ)) : ℂ :=
  (1 / (d : ℝ)) • ∑ r : Fin d, ∫ β in (0 : ℝ)..1, ∫ x, Φ β x ∂μ r

def mixedRiemann {d : ℕ} (n : ℕ) (μ : Fin d → Measure X)
    (Φ : ℝ → C(X, ℂ)) : ℂ :=
  (1 / (d : ℝ)) • ∑ r : Fin d, riemann n (fun β => ∫ x, Φ β x ∂μ r)

lemma mixed_riemann_error {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (μ : Fin d → Measure X) [∀ r, IsProbabilityMeasure (μ r)]
    (Φ : ℝ → C(X, ℂ)) (hΦ : Continuous Φ) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |x - y| ≤ 1 / (n : ℝ) → ‖Φ x - Φ y‖ ≤ ε) :
    ‖mixedRiemann n μ Φ - betaMixture μ Φ‖ ≤ ε := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [mixedRiemann, betaMixture, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hdR), ← Finset.sum_sub_distrib]
  calc
    _ ≤ (1 / (d : ℝ)) * ∑ _r : Fin d, ε := by
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hdR.le)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro r hr
      apply riemann_error hn _ (continuous_integral (μ r) Φ hΦ) hε
      intro x hx y hy hxy
      have hb := (integral_lipschitz (μ r)).dist_le_mul (Φ x) (Φ y)
      simp only [NNReal.coe_one, one_mul, dist_eq_norm] at hb
      exact hb.trans (hosc x hx y hy hxy)
    _ = ε := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

omit [CompactSpace X] [OpensMeasurableSpace X] in
 

lemma frozen_tendsto {ι : Type*} {l : Filter ι} {N : ι → ℕ}
    {d n : ℕ} (_hd : 0 < d) (hn : 0 < n)
    (q : (j : ι) → Fin (N j) → X) (μ : Fin d → Measure X)
    (Φ : ℝ → C(X, ℂ))
    (hlocal : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      ∀ (r : Fin d) (f : C(X, ℂ)),
      Tendsto (fun j => (1 / (N j : ℝ)) •
        ∑ k ∈ cell (N j) d r.val a b, f (q j k)) l
        (𝓝 (((b - a) / d) • ∫ x, f x ∂μ r))) :
    Tendsto (fun j => frozen n d (q j) Φ) l (𝓝 (mixedRiemann n μ Φ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpart (i : Fin n) (r : Fin d) :=
    hlocal ((i.val : ℝ) / n) (((i.val : ℝ) + 1) / n)
      (partition_endpoints hn i).1
      (div_lt_div_of_pos_right (by linarith) hnR)
      (partition_endpoints hn i).2.2 r (Φ ((i.val : ℝ) / n))
  have hlim := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun r _ => hpart i r))
  have heq : (∑ i : Fin n, ∑ r : Fin d,
      (((((i.val : ℝ) + 1) / n - (i.val : ℝ) / n) / d) •
        ∫ x, Φ ((i.val : ℝ) / n) x ∂μ r)) = mixedRiemann n μ Φ := by
    rw [mixedRiemann]
    simp only [riemann, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro r hr
    rw [smul_smul]
    congr 1
    ring
  rw [heq] at hlim
  simpa only [frozen, Finset.smul_sum] using hlim

 

omit [CompactSpace X] [OpensMeasurableSpace X] in
lemma local_mass_limit {ι : Type*} {l : Filter ι} {N : ι → ℕ}
    (hN : Tendsto N l atTop) {d : ℕ} (hd : 0 < d)
    (q : (j : ι) → Fin (N j) → X) (μ : Fin d → Measure X)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (r : Fin d) (f : C(X, ℂ))
    (hlocal : Tendsto (fun j => 𝔼 k ∈ cell (N j) d r.val a b, f (q j k)) l
      (𝓝 (∫ x, f x ∂μ r))) :
    Tendsto (fun j => (1 / (N j : ℝ)) •
      ∑ k ∈ cell (N j) d r.val a b, f (q j k)) l
      (𝓝 (((b - a) / d) • ∫ x, f x ∂μ r)) := by
  have hmass := (cell_density hd r.isLt ha hab hb).comp hN
  have ht := hmass.smul hlocal
  apply ht.congr
  intro j
  dsimp only [Function.comp_apply]
  set S := cell (N j) d r.val a b
  rw [← Finset.card_smul_expect S (fun k => f (q j k)),
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  ring

 

theorem global_point_law {ι : Type*} {l : Filter ι} {N : ι → ℕ}
    (hN : ∀ᶠ j in l, 0 < N j) {d : ℕ} (hd : 0 < d)
    (q : (j : ι) → Fin (N j) → X) (μ : Fin d → Measure X)
    [∀ r, IsProbabilityMeasure (μ r)]
    (Φ : ℝ → C(X, ℂ)) (hΦ : Continuous Φ)
    (hlocal : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      ∀ (r : Fin d) (f : C(X, ℂ)),
      Tendsto (fun j => (1 / (N j : ℝ)) •
        ∑ k ∈ cell (N j) d r.val a b, f (q j k)) l
        (𝓝 (((b - a) / d) • ∫ x, f x ∂μ r))) :
    Tendsto (fun j => empirical (q j) Φ) l (𝓝 (betaMixture μ Φ)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have huc : UniformContinuousOn Φ (Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hΦ.continuousOn
  obtain ⟨δ, hδ, huniform⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 4) (by positivity)
  obtain ⟨n, hnδ⟩ := exists_nat_one_div_lt hδ
  have hnunit : 1 / ((n + 1 : ℕ) : ℝ) < δ := by simpa using hnδ
  have hosc : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |x - y| ≤ 1 / ((n + 1 : ℕ) : ℝ) → ‖Φ x - Φ y‖ ≤ ε / 4 := by
    intro x hx y hy hxy
    have ht := huniform x hx y hy (by simpa only [Real.dist_eq] using hxy.trans_lt hnunit)
    simpa only [dist_eq_norm] using ht.le
  have he := mixed_riemann_error (Nat.succ_pos n) hd μ Φ hΦ (by positivity) hosc
  have ht := frozen_tendsto hd (Nat.succ_pos n) q μ Φ hlocal
  have hevent := Metric.tendsto_nhds.mp ht (ε / 2) (by positivity)
  filter_upwards [hN, hevent] with j hj hjdist
  have hfreeze := empirical_frozen_error (Nat.succ_pos n) hd hj (q j) Φ hosc
  have htri := dist_triangle (empirical (q j) Φ) (frozen (n + 1) d (q j) Φ)
    (betaMixture μ Φ)
  have htri' := dist_triangle (frozen (n + 1) d (q j) Φ)
    (mixedRiemann (n + 1) μ Φ) (betaMixture μ Φ)
  rw [← dist_eq_norm] at he hfreeze
  linarith

 

theorem global_point_law_of_local_haar {ι : Type*} {l : Filter ι} {N : ι → ℕ}
    (hN : Tendsto N l atTop) {d : ℕ} (hd : 0 < d)
    (q : (j : ι) → Fin (N j) → X) (μ : Fin d → Measure X)
    [∀ r, IsProbabilityMeasure (μ r)]
    (Φ : ℝ → C(X, ℂ)) (hΦ : Continuous Φ)
    (hlocal : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      ∀ (r : Fin d) (f : C(X, ℂ)),
      Tendsto (fun j => 𝔼 k ∈ cell (N j) d r.val a b, f (q j k)) l
        (𝓝 (∫ x, f x ∂μ r))) :
    Tendsto (fun j => empirical (q j) Φ) l (𝓝 (betaMixture μ Φ)) := by
  apply global_point_law (hN.eventually (eventually_gt_atTop 0)) hd q μ Φ hΦ
  intro a b ha hab hb r f
  exact local_mass_limit hN hd q μ ha hab.le hb r f (hlocal a b ha hab hb r f)

end Tests

end GlobalPointLaw
 

end
end

end OAI
