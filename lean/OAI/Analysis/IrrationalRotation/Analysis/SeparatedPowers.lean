import Mathlib

namespace OAI

namespace Invariant233.SeparatedPowers

open Filter
open scoped Topology

theorem exists_separated_subset {α : Type*} (s : Finset α) (R : α → α → Prop) [DecidableRel R]
    (hSymm : ∀ ⦃x y⦄, R x y → R y x) (D : ℕ)
    (hdegree : ∀ x ∈ s, (s.filter (R x)).card ≤ D) :
    ∃ t : Finset α, t ⊆ s ∧ (t : Set α).Pairwise (fun x y => ¬ R x y) ∧
      s.card ≤ t.card * (D + 1) := by
  classical
  let T := s.powerset.filter (fun t : Finset α =>
    (t : Set α).Pairwise (fun x y => ¬ R x y))
  have hTempty : (∅ : Finset α) ∈ T := by simp [T]
  obtain ⟨t, ht, hmax⟩ := T.exists_max_image Finset.card ⟨∅, hTempty⟩
  have hsub : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  have hpair : (t : Set α).Pairwise (fun x y => ¬ R x y) :=
    (Finset.mem_filter.mp ht).2
  have hcover : s ⊆ t.biUnion (fun y => insert y (s.filter (R y))) := by
    intro x hxs
    by_contra hxout
    have hxnot : x ∉ t := by
      intro hxt
      apply hxout
      exact Finset.mem_biUnion.mpr ⟨x, hxt, Finset.mem_insert_self _ _⟩
    have hbad : ∀ y ∈ t, ¬ R y x := by
      intro y hy hyx
      apply hxout
      exact Finset.mem_biUnion.mpr
        ⟨y, hy, Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hxs, hyx⟩)⟩
    have hnewpair : ((insert x t : Finset α) : Set α).Pairwise (fun a b => ¬ R a b) := by
      rw [Finset.coe_insert]
      apply hpair.insert
      intro y hy hxy
      exact ⟨fun h => hbad y hy (hSymm h), hbad y hy⟩
    have hnew : insert x t ∈ T := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr (Finset.insert_subset hxs hsub), hnewpair⟩
    have hc := hmax (insert x t) hnew
    rw [Finset.card_insert_of_notMem hxnot] at hc
    omega
  refine ⟨t, hsub, hpair, ?_⟩
  calc
    s.card ≤ (t.biUnion (fun y => insert y (s.filter (R y)))).card :=
      Finset.card_le_card hcover
    _ ≤ t.card * (D + 1) := by
      apply Finset.card_biUnion_le_card_mul
      intro y hy
      exact (Finset.card_insert_le y (s.filter (R y))).trans
        (Nat.add_le_add_right (hdegree y (hsub hy)) 1)

theorem power_gap_absorbs_polynomial {m C a b d : ℝ}
    (hm : 1 ≤ m) (hC : C ≤ m) (hgap : 1 + d ≤ (b - a) * m) :
    C * m ^ d * m ^ (a * m) ≤ m ^ (b * m) := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  calc
    C * m ^ d * m ^ (a * m) ≤ m * m ^ d * m ^ (a * m) := by
      gcongr
    _ = m ^ (1 + d + a * m) := by
      rw [Real.rpow_add hmpos, Real.rpow_add hmpos, Real.rpow_one]
    _ ≤ m ^ (b * m) :=
      Real.rpow_le_rpow_of_exponent_le hm (by linarith)

theorem eventually_power_gap {m : ℕ → ℝ} (hm : Tendsto m atTop atTop)
    (C a b d : ℝ) (hab : a < b) :
    ∀ᶠ n in atTop, C * m n ^ d * m n ^ (a * m n) ≤ m n ^ (b * m n) := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  filter_upwards [hm.eventually_ge_atTop 1, hm.eventually_ge_atTop C,
    hm.eventually_ge_atTop ((1 + d) / (b - a))] with n hn hC hd
  apply power_gap_absorbs_polynomial hn hC
  have := (div_le_iff₀ hgap).mp hd
  nlinarith

theorem eventually_sampling_count {m : ℕ → ℝ} (hm : Tendsto m atTop atTop)
    (c : ℝ) (hc : 0 < c) :
    ∀ᶠ n in atTop, m n ^ ((69 / 100 : ℝ) * m n) ≤
      c * m n ^ ((7 / 10 : ℝ) * m n) / m n ^ (1602 : ℝ) := by
  have h := eventually_power_gap hm (c⁻¹) (69 / 100) (7 / 10) 1602 (by norm_num)
  filter_upwards [h, hm.eventually_ge_atTop 1] with n hn hmone
  have hmpos : 0 < m n := lt_of_lt_of_le zero_lt_one hmone
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hmpos _)).mpr
  have hh := mul_le_mul_of_nonneg_left hn hc.le
  calc
    m n ^ ((69 / 100 : ℝ) * m n) * m n ^ (1602 : ℝ) =
        c * (c⁻¹ * m n ^ (1602 : ℝ) * m n ^ ((69 / 100 : ℝ) * m n)) := by
          field_simp
    _ ≤ c * m n ^ ((7 / 10 : ℝ) * m n) := hh

theorem card_small_affine_le (s : Finset ℤ) (a b : ℤ) (hb : b ≠ 0) (R : ℕ) :
    (s.filter (fun x => |a + b * x| ≤ (R : ℤ))).card ≤ 2 * R + 1 := by
  have hcard : (s.filter (fun x => |a + b * x| ≤ (R : ℤ))).card ≤
      (Finset.Icc (-(R : ℤ)) R).card := by
    apply Finset.card_le_card_of_injOn (fun x => a + b * x)
    · intro x hx
      exact Finset.mem_Icc.mpr (abs_le.mp (Finset.mem_filter.mp hx).2)
    · intro x hx y hy hxy
      exact mul_left_cancel₀ hb (add_left_cancel hxy)
  have hc : (Finset.Icc (-(R : ℤ)) R).card = 2 * R + 1 := by
    rw [Int.card_Icc]
    omega
  exact hc ▸ hcard

theorem exists_frequency_separated_subset (s : Finset ℤ) (H R : ℕ)
    (hs : ∀ n ∈ s, (R : ℤ) < n) :
    ∃ t : Finset ℤ, t ⊆ s ∧
      s.card ≤ t.card * ((2 * H + 1) ^ 2 * (2 * R + 1) + 1) ∧
      ∀ n ∈ t, ∀ n' ∈ t, n ≠ n' → ∀ v v' : ℤ,
        |v| ≤ (H : ℤ) → |v'| ≤ (H : ℤ) → (v ≠ 0 ∨ v' ≠ 0) →
        (R : ℤ) < |v * n + v' * n'| := by
  classical
  let I : Finset ℤ := Finset.Icc (-(H : ℤ)) H
  let F : Finset (ℤ × ℤ) := (I.product I).filter (fun p => p.1 ≠ 0 ∧ p.2 ≠ 0)
  let Bad : ℤ → ℤ → Prop := fun n n' =>
    ∃ p ∈ F, |p.1 * n + p.2 * n'| ≤ (R : ℤ)
  have hsymm : ∀ ⦃n n'⦄, Bad n n' → Bad n' n := by
    intro n n' h
    obtain ⟨⟨v, v'⟩, hf, hsmall⟩ := h
    have hp := Finset.mem_filter.mp hf
    have hi := Finset.mem_product.mp hp.1
    refine ⟨(v', v), Finset.mem_filter.mpr ?_, ?_⟩
    · exact ⟨Finset.mem_product.mpr ⟨hi.2, hi.1⟩, hp.2.2, hp.2.1⟩
    · simpa only [add_comm] using hsmall
  have hFcard : F.card ≤ (2 * H + 1) ^ 2 := by
    have hI : I.card = 2 * H + 1 := by
      dsimp [I]
      rw [Int.card_Icc]
      omega
    calc
      F.card ≤ (I.product I).card := Finset.card_filter_le _ _
      _ = (2 * H + 1) ^ 2 := by
        change (I ×ˢ I).card = _
        rw [Finset.card_product, hI, pow_two]
  have hdegree : ∀ n ∈ s, (s.filter (Bad n)).card ≤
      (2 * H + 1) ^ 2 * (2 * R + 1) := by
    intro n hn
    have hcover : s.filter (Bad n) ⊆
        F.biUnion (fun p => s.filter (fun n' => |p.1 * n + p.2 * n'| ≤ (R : ℤ))) := by
      intro n' hn'
      obtain ⟨hns, p, hp, hsmall⟩ := Finset.mem_filter.mp hn'
      exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hns, hsmall⟩⟩
    calc
      (s.filter (Bad n)).card ≤
          (F.biUnion (fun p => s.filter (fun n' => |p.1 * n + p.2 * n'| ≤ (R : ℤ)))).card :=
        Finset.card_le_card hcover
      _ ≤ F.card * (2 * R + 1) := by
        apply Finset.card_biUnion_le_card_mul
        intro p hp
        exact card_small_affine_le s (p.1 * n) p.2 (Finset.mem_filter.mp hp).2.2 R
      _ ≤ (2 * H + 1) ^ 2 * (2 * R + 1) := Nat.mul_le_mul_right _ hFcard
  obtain ⟨t, hts, hpair, hcard⟩ :=
    exists_separated_subset s Bad hsymm ((2 * H + 1) ^ 2 * (2 * R + 1)) hdegree
  refine ⟨t, hts, hcard, ?_⟩
  intro n hn n' hn' hne v v' hv hv' hnonzero
  have hnR := hs n (hts hn)
  have hnR' := hs n' (hts hn')
  have hn0 : 0 ≤ n := by omega
  have hn0' : 0 ≤ n' := by omega
  by_cases hv0 : v = 0
  · have hvn : v' ≠ 0 := hnonzero.resolve_left (not_not.mpr hv0)
    have hmul := mul_le_mul_of_nonneg_right (Int.one_le_abs hvn) hn0'
    rw [one_mul] at hmul
    simpa only [hv0, zero_mul, zero_add, abs_mul, abs_of_nonneg hn0'] using hnR'.trans_le hmul
  by_cases hv0' : v' = 0
  · have hmul := mul_le_mul_of_nonneg_right (Int.one_le_abs hv0) hn0
    rw [one_mul] at hmul
    simpa only [hv0', zero_mul, add_zero, abs_mul, abs_of_nonneg hn0] using hnR.trans_le hmul
  apply lt_of_not_ge
  intro hsmall
  apply hpair hn hn' hne
  refine ⟨(v, v'), Finset.mem_filter.mpr ?_, hsmall⟩
  exact ⟨Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr (abs_le.mp hv), Finset.mem_Icc.mpr (abs_le.mp hv')⟩,
    hv0, hv0'⟩

theorem deletion_budget_le {m N : ℕ} (hm : 1 ≤ m) (hN : N ≤ m ^ 2) :
    (2 * m ^ 300 + 1) ^ 2 * (2 * (N * m ^ 1000) + 1) + 1 ≤
      28 * m ^ 1602 := by
  have h300 : 1 ≤ m ^ 300 := one_le_pow₀ hm
  have h1002 : 1 ≤ m ^ 1002 := one_le_pow₀ hm
  have h1602 : 1 ≤ m ^ 1602 := one_le_pow₀ hm
  have hR : N * m ^ 1000 ≤ m ^ 1002 := by
    calc
      N * m ^ 1000 ≤ m ^ 2 * m ^ 1000 := Nat.mul_le_mul_right _ hN
      _ = m ^ 1002 := by rw [← pow_add]
  have hH : 2 * m ^ 300 + 1 ≤ 3 * m ^ 300 := by omega
  have hR' : 2 * (N * m ^ 1000) + 1 ≤ 3 * m ^ 1002 := by omega
  calc
    (2 * m ^ 300 + 1) ^ 2 * (2 * (N * m ^ 1000) + 1) + 1 ≤
        (3 * m ^ 300) ^ 2 * (3 * m ^ 1002) + 1 := by gcongr
    _ = 27 * m ^ 1602 + 1 := by
      simp only [mul_pow, ← pow_mul]
      ring_nf
    _ ≤ 28 * m ^ 1602 := by omega

theorem quarter_le_card_interval {Q : ℝ} (hQ : 4 ≤ Q) :
    Q / 4 ≤ ((Finset.Icc (⌈Q / 2⌉ : ℤ) ⌊Q⌋).card : ℝ) := by
  have hi : (⌊Q⌋ : ℤ) + 1 - ⌈Q / 2⌉ ≤
      ((Finset.Icc (⌈Q / 2⌉ : ℤ) ⌊Q⌋).card : ℤ) := by
    rw [Int.card_Icc]
    exact Int.self_le_toNat _
  have hr : (⌊Q⌋ : ℝ) + 1 - (⌈Q / 2⌉ : ℝ) ≤
      ((Finset.Icc (⌈Q / 2⌉ : ℤ) ⌊Q⌋).card : ℝ) := by exact_mod_cast hi
  have hf := Int.lt_floor_add_one Q
  have hc := Int.ceil_lt_add_one (Q / 2)
  linarith

theorem eventually_exists_sampling_powers :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, N ≤ m ^ 2 →
      ∃ t : Finset ℤ,
        (∀ n ∈ t, (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n ∧
          (n : ℝ) ≤ (m : ℝ) ^ ((7 / 10 : ℝ) * m)) ∧
        (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (t.card : ℝ) ∧
        (∀ n ∈ t, 0 < n) ∧
        ∀ n ∈ t, ∀ n' ∈ t, n ≠ n' → ∀ v v' : ℤ,
          |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
          (v ≠ 0 ∨ v' ≠ 0) → (N * m ^ 1000 : ℕ) < |v * n + v' * n'| := by
  have hm : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hcount := eventually_power_gap hm 112 (69 / 100) (7 / 10) 1602 (by norm_num)
  have hgrowth := eventually_power_gap hm 4 0 (7 / 10) 1002 (by norm_num)
  filter_upwards [hcount, hgrowth, eventually_ge_atTop 20] with m hcount hgrowth hm20
  intro N hN
  have hmone : 1 ≤ m := by omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  let Q : ℝ := (m : ℝ) ^ ((7 / 10 : ℝ) * m)
  let s : Finset ℤ := Finset.Icc (⌈Q / 2⌉ : ℤ) ⌊Q⌋
  have hQpos : 0 < Q := Real.rpow_pos_of_pos hmpos _
  have hQlarge : 4 ≤ Q := by
    have hp : 1 ≤ (m : ℝ) ^ (1002 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hmone) (by norm_num)
    simp only [zero_mul, Real.rpow_zero, mul_one] at hgrowth
    dsimp [Q]
    linarith
  have hR : N * m ^ 1000 ≤ m ^ 1002 := by
    calc
      N * m ^ 1000 ≤ m ^ 2 * m ^ 1000 := Nat.mul_le_mul_right _ hN
      _ = m ^ 1002 := by rw [← pow_add]
  have hRreal : (N * m ^ 1000 : ℕ) ≤ (m : ℝ) ^ (1002 : ℝ) := by
    rw [show (1002 : ℝ) = ((1002 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact_mod_cast hR
  have hRlt : ((N * m ^ 1000 : ℕ) : ℝ) < Q / 2 := by
    have hp := Real.rpow_pos_of_pos hmpos (1002 : ℝ)
    simp only [zero_mul, Real.rpow_zero, mul_one] at hgrowth
    dsimp [Q]
    linarith
  have hinterval : ∀ n ∈ s, Q / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ Q := by
    intro n hn
    have hmem := Finset.mem_Icc.mp hn
    constructor
    · exact (Int.le_ceil (Q / 2)).trans (by exact_mod_cast hmem.1)
    · exact (show (n : ℝ) ≤ (⌊Q⌋ : ℝ) by exact_mod_cast hmem.2).trans (Int.floor_le Q)
  obtain ⟨t, hts, hcard, hsep⟩ :=
    exists_frequency_separated_subset s (m ^ 300) (N * m ^ 1000) (by
      intro n hn
      have h := hRlt.trans_le (hinterval n hn).1
      exact_mod_cast h)
  have hcardreal : (s.card : ℝ) ≤ (t.card : ℝ) *
      (((2 * m ^ 300 + 1) ^ 2 * (2 * (N * m ^ 1000) + 1) + 1 : ℕ) : ℝ) :=
    by exact_mod_cast hcard
  have hbudget : (((2 * m ^ 300 + 1) ^ 2 * (2 * (N * m ^ 1000) + 1) + 1 : ℕ) : ℝ) ≤
      28 * (m : ℝ) ^ (1602 : ℝ) := by
    rw [show (1602 : ℝ) = ((1602 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact_mod_cast deletion_budget_le hmone hN
  have hcountlower : 28 * (m : ℝ) ^ (1602 : ℝ) *
      (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (s.card : ℝ) := by
    have hc := quarter_le_card_interval hQlarge
    change Q / 4 ≤ (s.card : ℝ) at hc
    dsimp [Q] at hc
    linarith
  have hselected : (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (t.card : ℝ) := by
    have hbound := hcardreal.trans (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg t.card))
    have hp : 0 < 28 * (m : ℝ) ^ (1602 : ℝ) := by positivity
    apply le_of_mul_le_mul_left _ hp
    calc
      28 * (m : ℝ) ^ (1602 : ℝ) * (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤
          (s.card : ℝ) := hcountlower
      _ ≤ 28 * (m : ℝ) ^ (1602 : ℝ) * (t.card : ℝ) := by
        simpa only [mul_comm] using hbound
  refine ⟨t, (fun n hn => hinterval n (hts hn)), hselected, ?_, hsep⟩
  intro n hn
  have h := (half_pos hQpos).trans_le (hinterval n (hts hn)).1
  exact_mod_cast h

theorem eventually_exists_nat_sampling_powers :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, N ≤ m ^ 2 →
      ∃ t : Finset ℕ,
        (∀ n ∈ t, (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n ∧
          (n : ℝ) ≤ (m : ℝ) ^ ((7 / 10 : ℝ) * m)) ∧
        (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (t.card : ℝ) ∧
        (∀ n ∈ t, 0 < n) ∧
        ∀ n ∈ t, ∀ n' ∈ t, n ≠ n' → ∀ v v' : ℤ,
          |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
          (v ≠ 0 ∨ v' ≠ 0) →
          (N * m ^ 1000 : ℕ) < |v * (n : ℤ) + v' * (n' : ℤ)| := by
  classical
  filter_upwards [eventually_exists_sampling_powers] with m hm
  intro N hN
  obtain ⟨t, hrange, hcard, hpos, hsep⟩ := hm N hN
  have hcast : ∀ n ∈ t, (n.toNat : ℤ) = n := by
    intro n hn
    exact Int.toNat_of_nonneg (hpos n hn).le
  have hcastReal : ∀ n ∈ t, (n.toNat : ℝ) = (n : ℝ) := by
    intro n hn
    exact_mod_cast hcast n hn
  have hcardImage : (t.image Int.toNat).card = t.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have h := congrArg (fun n : ℕ => (n : ℤ)) hab
    simpa only [hcast a ha, hcast b hb] using h
  refine ⟨t.image Int.toNat, ?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    simpa only [hcastReal z hz] using hrange z hz
  · simpa only [hcardImage] using hcard
  · intro n hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    have hzpos := hpos z hz
    omega
  · intro n hn n' hn' hne v v' hv hv' hvv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hn'
    have hzz : z ≠ z' := by intro h; exact hne (congrArg Int.toNat h)
    simpa only [hcast z hz, hcast z' hz'] using hsep z hz z' hz' hzz v v' hv hv' hvv

theorem exists_frequency_separated_nat_subset (s : Finset ℕ) (H R : ℕ)
    (hs : ∀ n ∈ s, R < n) :
    ∃ t : Finset ℕ, t ⊆ s ∧
      s.card ≤ t.card * ((2 * H + 1) ^ 2 * (2 * R + 1) + 1) ∧
      ∀ n ∈ t, ∀ n' ∈ t, n ≠ n' → ∀ v v' : ℤ,
        |v| ≤ (H : ℤ) → |v'| ≤ (H : ℤ) → (v ≠ 0 ∨ v' ≠ 0) →
        (R : ℤ) < |v * (n : ℤ) + v' * (n' : ℤ)| := by
  classical
  obtain ⟨u, hus, hcard, hsep⟩ :=
    exists_frequency_separated_subset (s.image (fun n : ℕ => (n : ℤ))) H R (by
      intro n hn
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
      exact_mod_cast hs k hk)
  have hnonneg : ∀ n ∈ u, 0 ≤ n := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (hus hn)
    exact Int.natCast_nonneg k
  have hcast : ∀ n ∈ u, (n.toNat : ℤ) = n :=
    fun n hn => Int.toNat_of_nonneg (hnonneg n hn)
  have hcardu : (u.image Int.toNat).card = u.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    have h := congrArg (fun n : ℕ => (n : ℤ)) hab
    simpa only [hcast a ha, hcast b hb] using h
  have hcards : (s.image (fun n : ℕ => (n : ℤ))).card = s.card :=
    Finset.card_image_of_injective _ (by intro a b h; change (a : ℤ) = (b : ℤ) at h; omega)
  refine ⟨u.image Int.toNat, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (hus hz)
    simpa using hk
  · simpa only [hcardu, hcards] using hcard
  · intro n hn n' hn' hne v v' hv hv' hvv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hn'
    have hzz : z ≠ z' := by intro h; exact hne (congrArg Int.toNat h)
    simpa only [hcast z hz, hcast z' hz'] using hsep z hz z' hz' hzz v v' hv hv' hvv

theorem eventually_select_from_supply (c : ℝ) (hc : 0 < c) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, N ≤ m ^ 2 → ∀ s : Finset ℕ,
      (∀ n ∈ s, N * m ^ 1000 < n) →
      c * (m : ℝ) ^ ((7 / 10 : ℝ) * m) ≤ (s.card : ℝ) →
      ∃ t : Finset ℕ, t ⊆ s ∧
        (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (t.card : ℝ) ∧
        ∀ n ∈ t, ∀ n' ∈ t, n ≠ n' → ∀ v v' : ℤ,
          |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
          (v ≠ 0 ∨ v' ≠ 0) →
          (N * m ^ 1000 : ℕ) < |v * (n : ℤ) + v' * (n' : ℤ)| := by
  have hm : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hgap := eventually_power_gap hm (28 / c) (69 / 100) (7 / 10) 1602 (by norm_num)
  filter_upwards [hgap, eventually_ge_atTop 1] with m hgap hmone
  intro N hN s hs hsize
  obtain ⟨t, hts, hcard, hsep⟩ :=
    exists_frequency_separated_nat_subset s (m ^ 300) (N * m ^ 1000) hs
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hbudget : (((2 * m ^ 300 + 1) ^ 2 * (2 * (N * m ^ 1000) + 1) + 1 : ℕ) : ℝ) ≤
      28 * (m : ℝ) ^ (1602 : ℝ) := by
    rw [show (1602 : ℝ) = ((1602 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact_mod_cast deletion_budget_le hmone hN
  have hcardreal : (s.card : ℝ) ≤ (t.card : ℝ) *
      (((2 * m ^ 300 + 1) ^ 2 * (2 * (N * m ^ 1000) + 1) + 1 : ℕ) : ℝ) :=
    by exact_mod_cast hcard
  have hlower : 28 * (m : ℝ) ^ (1602 : ℝ) *
      (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (s.card : ℝ) := by
    calc
      _ = c * ((28 / c) * (m : ℝ) ^ (1602 : ℝ) *
          (m : ℝ) ^ ((69 / 100 : ℝ) * m)) := by field_simp
      _ ≤ c * (m : ℝ) ^ ((7 / 10 : ℝ) * m) := mul_le_mul_of_nonneg_left hgap hc.le
      _ ≤ (s.card : ℝ) := hsize
  refine ⟨t, hts, ?_, hsep⟩
  have hp : 0 < 28 * (m : ℝ) ^ (1602 : ℝ) := by positivity
  apply le_of_mul_le_mul_left _ hp
  calc
    _ ≤ (s.card : ℝ) := hlower
    _ ≤ (t.card : ℝ) * (28 * (m : ℝ) ^ (1602 : ℝ)) :=
      hcardreal.trans (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg t.card))
    _ = _ := by ring

end Invariant233.SeparatedPowers

end OAI
