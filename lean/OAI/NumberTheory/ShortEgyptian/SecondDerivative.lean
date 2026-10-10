import OAI.NumberTheory.ShortEgyptian.FirstDerivative

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem discrete_difference_bounds (d : ℕ → ℝ) (N : ℕ) (lam Λ : ℝ)
    (hstep : ∀ n < N, lam ≤ d (n + 1) - d n ∧ d (n + 1) - d n ≤ Λ)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) :
    lam * ((j : ℝ) - i) ≤ d j - d i ∧ d j - d i ≤ Λ * ((j : ℝ) - i) := by
  have hlo : MonotoneOn (fun n : ℕ => d n - lam * n) (Set.Icc 0 N) := by
    apply monotoneOn_of_le_add_one Set.ordConnected_Icc
    intro n _ _ hn
    simp only [Set.mem_Icc] at hn
    have hs := (hstep n (by omega)).1
    push_cast
    nlinarith
  have hhi : AntitoneOn (fun n : ℕ => d n - Λ * n) (Set.Icc 0 N) := by
    apply antitoneOn_of_add_one_le Set.ordConnected_Icc
    intro n _ _ hn
    simp only [Set.mem_Icc] at hn
    have hs := (hstep n (by omega)).2
    push_cast
    nlinarith
  have h1 := hlo ⟨Nat.zero_le _, hij.trans hj⟩ ⟨Nat.zero_le _, hj⟩ hij
  have h2 := hhi ⟨Nat.zero_le _, hij.trans hj⟩ ⟨Nat.zero_le _, hj⟩ hij
  constructor <;> linarith

theorem separated_band_card (d : ℕ → ℝ) (N : ℕ) {lam a b : ℝ}
    (hlam : 0 < lam) (hab : a ≤ b)
    (hsep : ∀ i j, i ≤ j → j ≤ N → lam * ((j : ℝ) - i) ≤ d j - d i)
    (s : Finset ℕ) (hs : ∀ n ∈ s, n ≤ N ∧ a ≤ d n ∧ d n ≤ b) :
    (s.card : ℝ) ≤ (b - a) / lam + 1 := by
  classical
  by_cases hne : s.Nonempty
  · let p := s.min' hne
    let r := s.max' hne
    have hp : p ∈ s := s.min'_mem hne
    have hr : r ∈ s := s.max'_mem hne
    have hpr : p ≤ r := s.min'_le _ hr
    have hsub : s ⊆ Icc p r := fun n hn => mem_Icc.mpr
      ⟨s.min'_le _ hn, s.le_max' _ hn⟩
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hc
    have hc' : (s.card : ℝ) ≤ (r : ℝ) + 1 - p := by
      have : (s.card : ℝ) ≤ ((r + 1 - p : ℕ) : ℝ) := by exact_mod_cast hc
      simpa only [Nat.cast_sub (by omega : p ≤ r + 1), Nat.cast_add, Nat.cast_one] using this
    have hd := hsep p r hpr (hs r hr).1
    have hd' : lam * ((r : ℝ) - p) ≤ b - a := by
      linarith [(hs p hp).2.1, (hs r hr).2.2]
    have hd'' := (le_div_iff₀ hlam).mpr (show ((r : ℝ) - p) * lam ≤ b - a by nlinarith)
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [card_empty, Nat.cast_zero]
    positivity

theorem phase_sum_first_derivative_Icc {β : ℝ} (hβ : 0 < β)
    (f : ℕ → ℝ) (q : ℤ) (p r : ℕ) (hpr : p ≤ r)
    (hlow : ∀ n ∈ Icc p r, β ≤ f (n + 1) - f n - q)
    (hupp : ∀ n ∈ Icc p r, f (n + 1) - f n - q ≤ 1 - β)
    (hmono : ∀ n ∈ Ico p r, f (n + 1) - f n ≤ f (n + 2) - f (n + 1)) :
    ‖∑ n ∈ Icc p r, phase (f n)‖ ≤ 1 / β + 1 := by
  have hs := phase_sum_first_derivative hβ (fun n => f (p + n)) q (r - p)
    (fun n hn => by simpa [Nat.add_assoc] using hlow (p + n) (mem_Icc.mpr ⟨by omega, by omega⟩))
    (fun n hn => by simpa [Nat.add_assoc] using hupp (p + n) (mem_Icc.mpr ⟨by omega, by omega⟩))
    (fun n hn => by simpa [Nat.add_assoc] using hmono (p + n) (mem_Ico.mpr ⟨by omega, by omega⟩))
  rw [← Finset.sum_Ico_eq_sum_range (fun n => phase (f n)) p r] at hs
  have heq : (∑ n ∈ Icc p r, phase (f n)) =
      (∑ n ∈ Ico p r, phase (f n)) + phase (f r) := by
    rw [← Ico_add_one_right_eq_Icc, sum_Ico_succ_top hpr]
  rw [heq]
  exact (norm_add_le _ _).trans (by simpa using add_le_add_right hs 1)

theorem phase_sum_in_good_band {β : ℝ} (hβ : 0 < β)
    (f : ℕ → ℝ) (q : ℤ) (N : ℕ)
    (hmono : MonotoneOn (fun n => f (n + 1) - f n) (Set.Icc 0 N)) :
    ‖∑ n ∈ (range (N + 1)).filter (fun n =>
      (q : ℝ) + β ≤ f (n + 1) - f n ∧ f (n + 1) - f n ≤ q + 1 - β),
      phase (f n)‖ ≤ 1 / β + 1 := by
  classical
  let s := (range (N + 1)).filter (fun n =>
    (q : ℝ) + β ≤ f (n + 1) - f n ∧ f (n + 1) - f n ≤ q + 1 - β)
  change ‖∑ n ∈ s, phase (f n)‖ ≤ _
  by_cases hne : s.Nonempty
  · let p := s.min' hne
    let r := s.max' hne
    have hp : p ∈ s := s.min'_mem hne
    have hr : r ∈ s := s.max'_mem hne
    have hp' := mem_filter.mp hp
    have hr' := mem_filter.mp hr
    have hpr : p ≤ r := s.min'_le _ hr
    have heq : s = Icc p r := by
      ext n
      constructor
      · intro hn
        exact mem_Icc.mpr ⟨s.min'_le _ hn, s.le_max' _ hn⟩
      · intro hn
        obtain ⟨hpn, hnr⟩ := mem_Icc.mp hn
        have hrN : r ≤ N := by simpa only [mem_range, Nat.lt_succ_iff] using hr'.1
        have hpn' := hmono ⟨Nat.zero_le _, hpr.trans hrN⟩
          ⟨Nat.zero_le _, hnr.trans hrN⟩ hpn
        have hnr' := hmono ⟨Nat.zero_le _, hnr.trans hrN⟩ ⟨Nat.zero_le _, hrN⟩ hnr
        apply mem_filter.mpr
        exact ⟨mem_range.mpr (by omega), hp'.2.1.trans hpn', hnr'.trans hr'.2.2⟩
    have hrN : r ≤ N := by simpa only [mem_range, Nat.lt_succ_iff] using hr'.1
    rw [heq]
    apply phase_sum_first_derivative_Icc hβ f q p r hpr
    · intro n hn
      have := (mem_filter.mp (heq.symm ▸ hn)).2.1
      linarith
    · intro n hn
      have := (mem_filter.mp (heq.symm ▸ hn)).2.2
      linarith
    · intro n hn
      obtain ⟨_, hnr⟩ := mem_Ico.mp hn
      exact hmono ⟨Nat.zero_le _, by omega⟩ ⟨Nat.zero_le _, by omega⟩ (Nat.le_succ n)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [sum_empty, norm_zero]
    positivity

theorem phase_sum_one_bin (f : ℕ → ℝ) (N : ℕ) (q : ℤ) {lam β : ℝ}
    (hlam : 0 < lam) (hβ : 0 < β)
    (hsep : ∀ i j, i ≤ j → j ≤ N →
      lam * ((j : ℝ) - i) ≤ (f (j + 1) - f j) - (f (i + 1) - f i)) :
    ‖∑ n ∈ (range (N + 1)).filter (fun n => ⌊f (n + 1) - f n⌋ = q), phase (f n)‖ ≤
      2 * β / lam + 1 / β + 3 := by
  classical
  let d (n : ℕ) := f (n + 1) - f n
  let t := (range (N + 1)).filter (fun n => ⌊d n⌋ = q)
  let g := (range (N + 1)).filter (fun n => (q : ℝ) + β ≤ d n ∧ d n ≤ q + 1 - β)
  let lo := (range (N + 1)).filter (fun n => (q : ℝ) ≤ d n ∧ d n ≤ q + β)
  let hi := (range (N + 1)).filter (fun n => (q : ℝ) + 1 - β ≤ d n ∧ d n ≤ q + 1)
  have hmono : MonotoneOn d (Set.Icc 0 N) := by
    intro i hi j hj hij
    have hh := hsep i j hij hj.2
    have hh' : 0 ≤ lam * ((j : ℝ) - i) := mul_nonneg hlam.le (sub_nonneg.mpr (by exact_mod_cast hij))
    linarith
  have hg : g ⊆ t := by
    intro n hn
    obtain ⟨hnN, h1, h2⟩ := mem_filter.mp hn
    apply mem_filter.mpr ⟨hnN, ?_⟩
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  have hlo : (lo.card : ℝ) ≤ β / lam + 1 := by
    have hh := separated_band_card d N hlam (show (q : ℝ) ≤ q + β by linarith)
      hsep lo (fun n hn => by
        obtain ⟨hnN, h1, h2⟩ := mem_filter.mp hn
        exact ⟨by simpa only [mem_range, Nat.lt_succ_iff] using hnN, h1, h2⟩)
    simpa only [add_sub_cancel_left] using hh
  have hhi : (hi.card : ℝ) ≤ β / lam + 1 := by
    have hh := separated_band_card d N hlam
      (show (q : ℝ) + 1 - β ≤ q + 1 by linarith) hsep hi (fun n hn => by
        obtain ⟨hnN, h1, h2⟩ := mem_filter.mp hn
        exact ⟨by simpa only [mem_range, Nat.lt_succ_iff] using hnN, h1, h2⟩)
    convert hh using 1; ring
  have hbsub : t \ g ⊆ lo ∪ hi := by
    intro n hn
    obtain ⟨hnt, hng⟩ := mem_sdiff.mp hn
    obtain ⟨hnN, hnq⟩ := mem_filter.mp hnt
    have hq := Int.floor_eq_iff.mp hnq
    have hn' : ¬((q : ℝ) + β ≤ d n ∧ d n ≤ q + 1 - β) := by
      intro hh
      exact hng (mem_filter.mpr ⟨hnN, hh⟩)
    by_cases hlow : (q : ℝ) + β ≤ d n
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hnN, (lt_of_not_ge (fun h => hn' ⟨hlow, h⟩)).le, hq.2.le⟩))
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hnN, hq.1, (lt_of_not_ge hlow).le⟩))
  have hbc : ((t \ g).card : ℝ) ≤ 2 * β / lam + 2 := by
    have hc := (Finset.card_le_card hbsub).trans (Finset.card_union_le lo hi)
    have hc' : ((t \ g).card : ℝ) ≤ lo.card + hi.card := by exact_mod_cast hc
    have heq : β / lam + 1 + (β / lam + 1) = 2 * β / lam + 2 := by ring
    linarith
  have hgn : ‖∑ n ∈ g, phase (f n)‖ ≤ 1 / β + 1 :=
    phase_sum_in_good_band hβ f q N hmono
  have hbn : ‖∑ n ∈ t \ g, phase (f n)‖ ≤ ((t \ g).card : ℝ) := by
    simpa using (norm_sum_le (t \ g) (fun n => phase (f n)))
  change ‖∑ n ∈ t, phase (f n)‖ ≤ _
  rw [← Finset.sum_sdiff (f := fun n => phase (f n)) hg]
  exact (norm_add_le _ _).trans (by linarith)

theorem phase_sum_second_derivative (f : ℕ → ℝ) (N : ℕ) {lam Λ β : ℝ}
    (hlam : 0 < lam) (hβ : 0 < β)
    (hstep : ∀ n < N,
      lam ≤ (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ∧
      (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ≤ Λ) :
    ‖∑ n ∈ range (N + 1), phase (f n)‖ ≤
      (Λ * N + 2) * (2 * β / lam + 1 / β + 3) := by
  classical
  let d (n : ℕ) := f (n + 1) - f n
  have hbounds {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) :=
    discrete_difference_bounds d N lam Λ (by simpa only [d, Nat.add_assoc] using hstep) hij hj
  have hdmono : MonotoneOn d (Set.Icc 0 N) := by
    intro i hi j hj hij
    have hh := (hbounds hij hj.2).1
    have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
    nlinarith
  let qs := Icc ⌊d 0⌋ ⌊d N⌋
  have hqN : ⌊d 0⌋ ≤ ⌊d N⌋ := Int.floor_mono (hdmono ⟨le_rfl, Nat.zero_le _⟩ ⟨Nat.zero_le _, le_rfl⟩ (Nat.zero_le _))
  have hmem (n : ℕ) (hn : n ∈ range (N + 1)) : ⌊d n⌋ ∈ qs := by
    have hnN : n ≤ N := by simpa only [mem_range, Nat.lt_succ_iff] using hn
    exact mem_Icc.mpr ⟨Int.floor_mono (hdmono ⟨le_rfl, Nat.zero_le _⟩ ⟨Nat.zero_le _, hnN⟩ (Nat.zero_le _)),
      Int.floor_mono (hdmono ⟨Nat.zero_le _, hnN⟩ ⟨Nat.zero_le _, le_rfl⟩ hnN)⟩
  have hcard : (qs.card : ℝ) ≤ Λ * N + 2 := by
    have hc : (qs.card : ℝ) = (⌊d N⌋ : ℝ) + 1 - (⌊d 0⌋ : ℝ) := by
      dsimp only [qs]
      rw [Int.card_Icc]
      have hh := Int.toNat_of_nonneg (show 0 ≤ ⌊d N⌋ + 1 - ⌊d 0⌋ by omega)
      exact_mod_cast hh
    rw [hc]
    have h1 := Int.floor_le (d N)
    have h0 := Int.lt_floor_add_one (d 0)
    have hh := (hbounds (Nat.zero_le N) le_rfl).2
    simp only [Nat.cast_zero, sub_zero] at hh
    linarith
  have hper (q : ℤ) : ‖∑ n ∈ (range (N + 1)).filter (fun n => ⌊d n⌋ = q), phase (f n)‖ ≤
      2 * β / lam + 1 / β + 3 :=
    phase_sum_one_bin f N q hlam hβ (fun i j hij hj => (hbounds hij hj).1)
  rw [← Finset.sum_fiberwise_of_maps_to hmem (fun n => phase (f n))]
  calc
    _ ≤ ∑ q ∈ qs, ‖∑ n ∈ range (N + 1) with ⌊d n⌋ = q, phase (f n)‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ qs, (2 * β / lam + 1 / β + 3) := sum_le_sum (fun q _ => hper q)
    _ = (qs.card : ℝ) * (2 * β / lam + 1 / β + 3) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

end ShortEgyptian

end OAI
