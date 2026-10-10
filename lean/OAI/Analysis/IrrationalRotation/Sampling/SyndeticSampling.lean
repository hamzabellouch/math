import Mathlib
import OAI.Analysis.IrrationalRotation.Analysis.OrbitPartition
import OAI.Analysis.IrrationalRotation.Analysis.SeparatedPowers

namespace OAI

namespace Invariant233.SyndeticSampling

theorem card_hits_in_blocks {P : ℕ → Prop} [DecidablePred P] (L : ℕ)
    (hhit : ∀ k : ℕ, ∃ r : ℕ, r ≤ L ∧ P (k + r)) (a M : ℕ) :
    M ≤ ((Finset.Ico a (a + M * (L + 1))).filter P).card := by
  classical
  choose r hr hP using hhit
  let f : ℕ → ℕ := fun i => a + i * (L + 1) + r (a + i * (L + 1))
  have hupper (i : ℕ) : f i < a + (i + 1) * (L + 1) := by
    dsimp [f]
    have := hr (a + i * (L + 1))
    nlinarith
  have hlower (i : ℕ) : a + i * (L + 1) ≤ f i := by
    dsimp [f]
    omega
  have hstrict : StrictMono f := by
    intro i j hij
    have hmul := Nat.mul_le_mul_right (L + 1) (show i + 1 ≤ j by omega)
    exact (hupper i).trans_le ((Nat.add_le_add_left hmul a).trans (hlower j))
  have hsub : (Finset.range M).image f ⊆
      (Finset.Ico a (a + M * (L + 1))).filter P := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    have hiM : i < M := Finset.mem_range.mp hi
    have hmul := Nat.mul_le_mul_right (L + 1) (show i + 1 ≤ M by omega)
    apply Finset.mem_filter.mpr
    constructor
    · refine Finset.mem_Ico.mpr ⟨?_, (hupper i).trans_le (Nat.add_le_add_left hmul a)⟩
      exact (Nat.le_add_right a (i * (L + 1))).trans (hlower i)
    · exact hP (a + i * (L + 1))
  have hcard : ((Finset.range M).image f).card = M := by
    rw [Finset.card_image_of_injective _ hstrict.injective, Finset.card_range]
  calc
    M = ((Finset.range M).image f).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

theorem card_hits_in_half_interval {P : ℕ → Prop} [DecidablePred P] (L : ℕ)
    (hhit : ∀ k : ℕ, ∃ r : ℕ, r ≤ L ∧ P (k + r))
    {Q : ℝ} (hQ : 8 * ((L : ℝ) + 1) ≤ Q) :
    Q / (8 * ((L : ℝ) + 1)) ≤
      (((Finset.Icc ⌈Q / 2⌉₊ ⌊Q⌋₊).filter P).card : ℝ) := by
  let a : ℕ := ⌈Q / 2⌉₊
  let M : ℕ := ⌊Q / (4 * ((L : ℝ) + 1))⌋₊
  have hL : 0 < (L : ℝ) + 1 := by positivity
  have hQ0 : 0 ≤ Q := by nlinarith
  have hMlo : Q / (4 * ((L : ℝ) + 1)) - 1 < (M : ℝ) := by
    exact Nat.sub_one_lt_floor _
  have hMhi : (M : ℝ) ≤ Q / (4 * ((L : ℝ) + 1)) :=
    Nat.floor_le (by positivity)
  have ha : (a : ℝ) < Q / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hMbound : (M : ℝ) * ((L : ℝ) + 1) ≤ Q / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    have h := (le_div_iff₀ (show 0 < 4 * ((L : ℝ) + 1) by positivity)).mp hMhi
    nlinarith
  have hend : ((a + M * (L + 1) : ℕ) : ℝ) ≤ Q := by
    push_cast
    nlinarith
  have hsub : ((Finset.Ico a (a + M * (L + 1))).filter P) ⊆
      (Finset.Icc ⌈Q / 2⌉₊ ⌊Q⌋₊).filter P := by
    intro n hn
    obtain ⟨hni, hpn⟩ := Finset.mem_filter.mp hn
    obtain ⟨han, hne⟩ := Finset.mem_Ico.mp hni
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨han, ?_⟩, hpn⟩
    apply Nat.le_floor
    exact (show (n : ℝ) ≤ ((a + M * (L + 1) : ℕ) : ℝ) by exact_mod_cast hne.le).trans hend
  have hcard := (card_hits_in_blocks L hhit a M).trans (Finset.card_le_card hsub)
  have hcardReal : (M : ℝ) ≤
      (((Finset.Icc ⌈Q / 2⌉₊ ⌊Q⌋₊).filter P).card : ℝ) := by exact_mod_cast hcard
  have hratio : 2 ≤ Q / (4 * ((L : ℝ) + 1)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have hdouble : Q / (4 * ((L : ℝ) + 1)) = 2 * (Q / (8 * ((L : ℝ) + 1))) := by
    field_simp
    ring
  linarith

theorem exists_uniform_hitting_window {θ : ℝ} (hθ : Irrational θ)
    (O : Set (AddCircle (1 : ℝ))) (hO : IsOpen O) (hOne : O.Nonempty) :
    ∃ L : ℕ, ∀ x : AddCircle (1 : ℝ), ∃ r : ℕ, r ≤ L ∧
      x + r • (θ : AddCircle (1 : ℝ)) ∈ O := by
  classical
  obtain ⟨L, φ, hnonneg, hsum, hsupport, hzero⟩ :=
    Invariant233.exists_irrational_rotation_partition hθ O hO hOne
  refine ⟨L, ?_⟩
  intro x
  have hsumne : (∑ r ∈ Finset.range (L + 1), φ r x) ≠ 0 := by
    rw [hsum x]
    norm_num
  obtain ⟨r, hr, hφ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
  refine ⟨r, Nat.le_of_lt_succ (Finset.mem_range.mp hr), ?_⟩
  exact hsupport r ⟨x, subset_tsupport (φ r) hφ, rfl⟩

theorem exists_uniform_phase_hitting_window {θ : ℝ} (hθ : Irrational θ)
    (t ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, ∀ k : ℕ, ∃ r : ℕ, r ≤ L ∧
      Int.fract (((k + r : ℕ) : ℝ) * θ - t) ∈ Set.Ioo 0 ε := by
  let O : Set (AddCircle (1 : ℝ)) :=
    (fun z : ℝ => (z : AddCircle (1 : ℝ))) '' Set.Ioo 0 (min ε 1)
  have hO : IsOpen O := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hOne : O.Nonempty :=
    (Set.nonempty_Ioo.mpr (lt_min hε zero_lt_one)).image _
  obtain ⟨L, hL⟩ := exists_uniform_hitting_window hθ O hO hOne
  refine ⟨L, ?_⟩
  intro k
  obtain ⟨r, hr, hmem⟩ := hL ((((k : ℝ) * θ - t) : ℝ) : AddCircle (1 : ℝ))
  obtain ⟨z, hz, hze⟩ := hmem
  have he : ((((k + r : ℕ) : ℝ) * θ - t : ℝ) : AddCircle (1 : ℝ)) =
      ((((k : ℝ) * θ - t) : ℝ) : AddCircle (1 : ℝ)) +
        r • (θ : AddCircle (1 : ℝ)) := by
    rw [← AddCircle.coe_nsmul, nsmul_eq_mul, ← AddCircle.coe_add]
    congr 1
    push_cast
    ring
  have hf : Int.fract z = Int.fract (((k + r : ℕ) : ℝ) * θ - t) := by
    have h := congrArg (fun x : AddCircle (1 : ℝ) =>
      (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)) (hze.trans he.symm)
    simpa only [AddCircle.coe_equivIco_mk_apply, div_one, mul_one] using h
  have hz01 : 0 ≤ z ∧ z < 1 := ⟨hz.1.le, hz.2.trans_le (min_le_right ε 1)⟩
  rw [Int.fract_eq_self.mpr hz01] at hf
  refine ⟨r, hr, ?_⟩
  rw [← hf]
  exact ⟨hz.1, hz.2.trans_le (min_le_left ε 1)⟩

open Filter
open scoped Topology

theorem tendsto_sampling_horizon :
    Tendsto (fun m : ℕ => (m : ℝ) ^ ((7 / 10 : ℝ) * m)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 20] with m hm
  have hmr : (20 : ℝ) ≤ m := by exact_mod_cast hm
  have h := Real.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ) ≤ m by linarith) (show (1 : ℝ) ≤ (7 / 10 : ℝ) * m by linarith)
  simpa only [Real.rpow_one] using h

theorem eventually_exists_prescribed_phase_sampling_powers {θ : ℝ}
    (hθ : Irrational θ) (shift width : ℝ) (hwidth : 0 < width) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, N ≤ m ^ 2 →
      ∃ t : Finset ℕ,
        (∀ n ∈ t, (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n ∧
          (n : ℝ) ≤ (m : ℝ) ^ ((7 / 10 : ℝ) * m)) ∧
        (∀ n ∈ t, Int.fract ((n : ℝ) * θ - shift) ∈ Set.Ioo 0 width) ∧
        (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ (t.card : ℝ) ∧
        (∀ n ∈ t, 0 < n) ∧
        ∀ n ∈ t, ∀ n' ∈ t, n ≠ n' → ∀ v v' : ℤ,
          |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
          (v ≠ 0 ∨ v' ≠ 0) →
          (N * m ^ 1000 : ℕ) < |v * (n : ℤ) + v' * (n' : ℤ)| := by
  classical
  obtain ⟨L, hL⟩ := exists_uniform_phase_hitting_window hθ shift width hwidth
  let c : ℝ := 1 / (8 * ((L : ℝ) + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hselection := SeparatedPowers.eventually_select_from_supply c hc
  have hm : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hgrowth := SeparatedPowers.eventually_power_gap hm 4 0 (7 / 10) 1002 (by norm_num)
  filter_upwards [hselection, hgrowth,
    tendsto_sampling_horizon.eventually_ge_atTop (8 * ((L : ℝ) + 1)),
    eventually_ge_atTop 20] with m hselect hgrowth hQlarge hm20
  intro N hN
  let Q : ℝ := (m : ℝ) ^ ((7 / 10 : ℝ) * m)
  let P : ℕ → Prop := fun n => Int.fract ((n : ℝ) * θ - shift) ∈ Set.Ioo 0 width
  let s : Finset ℕ := (Finset.Icc ⌈Q / 2⌉₊ ⌊Q⌋₊).filter P
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hQpos : 0 < Q := Real.rpow_pos_of_pos hmpos _
  have hinterval : ∀ n ∈ s, Q / 2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ Q := by
    intro n hn
    have hni := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    constructor
    · exact (Nat.le_ceil (Q / 2)).trans (by exact_mod_cast hni.1)
    · exact (show (n : ℝ) ≤ (⌊Q⌋₊ : ℝ) by exact_mod_cast hni.2).trans (Nat.floor_le hQpos.le)
  have hsize : c * Q ≤ (s.card : ℝ) := by
    have h := card_hits_in_half_interval (P := P) L hL (Q := Q) hQlarge
    simpa only [s, P, c, div_eq_mul_inv, one_mul, mul_comm] using h
  have hR : N * m ^ 1000 ≤ m ^ 1002 := by
    calc
      N * m ^ 1000 ≤ m ^ 2 * m ^ 1000 := Nat.mul_le_mul_right _ hN
      _ = m ^ 1002 := by rw [← pow_add]
  have hRreal : ((N * m ^ 1000 : ℕ) : ℝ) ≤ (m : ℝ) ^ (1002 : ℝ) := by
    rw [show (1002 : ℝ) = ((1002 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact_mod_cast hR
  have hRlt : ((N * m ^ 1000 : ℕ) : ℝ) < Q / 2 := by
    have hp := Real.rpow_pos_of_pos hmpos (1002 : ℝ)
    simp only [zero_mul, Real.rpow_zero, mul_one] at hgrowth
    dsimp [Q]
    linarith
  obtain ⟨t, hts, hcard, hsep⟩ := hselect N hN s (by
    intro n hn
    have h := hRlt.trans_le (hinterval n hn).1
    exact_mod_cast h) hsize
  refine ⟨t, (fun n hn => hinterval n (hts hn)), ?_, hcard, ?_, hsep⟩
  · intro n hn
    exact (Finset.mem_filter.mp (hts hn)).2
  · intro n hn
    have h := (half_pos hQpos).trans_le (hinterval n (hts hn)).1
    exact_mod_cast h

theorem eventually_exists_simultaneous_phase_sampling_powers {θ : ℝ}
    (hθ : Irrational θ) (q : ℕ) (shift width : Fin q → ℝ)
    (hwidth : ∀ r, 0 < width r) :
    ∀ᶠ m : ℕ in atTop, ∀ N : ℕ, N ≤ m ^ 2 →
      ∃ t : Fin q → Finset ℕ, ∀ r : Fin q,
        (∀ n ∈ t r, (m : ℝ) ^ ((7 / 10 : ℝ) * m) / 2 ≤ n ∧
          (n : ℝ) ≤ (m : ℝ) ^ ((7 / 10 : ℝ) * m)) ∧
        (∀ n ∈ t r, Int.fract ((n : ℝ) * θ - shift r) ∈ Set.Ioo 0 (width r)) ∧
        (m : ℝ) ^ ((69 / 100 : ℝ) * m) ≤ ((t r).card : ℝ) ∧
        (∀ n ∈ t r, 0 < n) ∧
        ∀ n ∈ t r, ∀ n' ∈ t r, n ≠ n' → ∀ v v' : ℤ,
          |v| ≤ (m ^ 300 : ℕ) → |v'| ≤ (m ^ 300 : ℕ) →
          (v ≠ 0 ∨ v' ≠ 0) →
          (N * m ^ 1000 : ℕ) < |v * (n : ℤ) + v' * (n' : ℤ)| := by
  classical
  have hall := Filter.eventually_all.mpr (fun r : Fin q =>
    eventually_exists_prescribed_phase_sampling_powers hθ (shift r) (width r) (hwidth r))
  filter_upwards [hall] with m hm
  intro N hN
  choose t ht using (fun r : Fin q => hm r N hN)
  exact ⟨t, ht⟩

end Invariant233.SyndeticSampling

end OAI
