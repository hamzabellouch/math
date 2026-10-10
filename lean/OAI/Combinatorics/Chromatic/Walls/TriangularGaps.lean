import Mathlib

namespace OAI

section
namespace ElementaryPositivity.TriangularGaps

structure Recurrence (n : ℕ) where
  u : ℕ → ℕ → ℕ
  T : ℕ → ℕ → ℕ
  xi : ℕ → ℕ → ℕ
  u_out : ∀ j i, ¬(1 ≤ j ∧ j ≤ i ∧ i ≤ n) → u j i = 0
  T_out : ∀ j i, ¬(1 ≤ j ∧ j ≤ i ∧ i ≤ n) → T j i = 0
  diagonal : ∀ j i, 1 ≤ j → j ≤ i → i ≤ n →
    u j i = T j i + u (j + 1) (i + 1)
  row : ∀ j i, 1 ≤ j → j ≤ i → i < n →
    T j (i + 1) + xi j (i + 1) = T j i
  start : ∀ j, 1 ≤ j → j ≤ n →
    T j j + xi j j + u 1 j = (if j = 1 then 1 else 0) + u 1 (j - 1)

namespace Recurrence

variable {n : ℕ} (R : Recurrence n)

lemma diagonal_all (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
    R.u j i = R.T j i + R.u (j + 1) (i + 1) := by
  by_cases hi : i ≤ n
  · exact R.diagonal j i hj hji hi
  · rw [R.u_out j i (by omega), R.T_out j i (by omega),
      R.u_out (j + 1) (i + 1) (by omega)]

lemma row_mono_add (j i k : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hik : i + k ≤ n) :
    R.T j (i + k) ≤ R.T j i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := R.row j (i + k) hj (by omega) (by omega)
    have h' := ih (by omega)
    have he : i + (k + 1) = i + k + 1 := by omega
    rw [he]
    omega

lemma row_le_start (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : i ≤ n) :
    R.T j i ≤ R.T j j := by
  simpa [Nat.add_sub_of_le hji] using
    R.row_mono_add j j (i - j) hj le_rfl (by omega)

lemma partial_total (i : ℕ) (hi : i ≤ n) :
    (∑ k ∈ Finset.range i, (R.T (k+1) (k+1) + R.xi (k+1) (k+1))) + R.u 1 i =
      if i = 0 then 0 else 1 := by
  induction i with
  | zero => simp [R.u_out 1 0 (by omega)]
  | succ i ih =>
    have hp := ih (by omega)
    have hs := R.start (i+1) (by omega) hi
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel] at hs
    by_cases hiz : i = 0
    · subst i
      simpa [R.u_out 1 0 (by omega)] using hs
    · simp only [ite_eq_right hiz] at hp
      simp only [ite_eq_right (show i + 1 ≠ 1 by omega), zero_add] at hs
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
      omega

lemma total_le_one :
    (∑ k ∈ Finset.range n, (R.T (k+1) (k+1) + R.xi (k+1) (k+1))) ≤ 1 := by
  have h := R.partial_total n le_rfl
  split_ifs at h <;> omega

lemma unique_start (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) (hpos : 0 < R.T s s) :
    R.T s s = 1 ∧
    (∀ j, 1 ≤ j → j ≤ n → R.T j j = if j = s then 1 else 0) ∧
    (∀ j, 1 ≤ j → j ≤ n → R.xi j j = 0) := by
  have h := Finset.sum_le_one_iff.mp R.total_le_one
  have hsi : s - 1 ∈ Finset.range n := by simp; omega
  have hs1 : s - 1 + 1 = s := by omega
  have hsp : R.T (s-1+1) (s-1+1) + R.xi (s-1+1) (s-1+1) ≠ 0 := by
    rw [hs1]; omega
  have hone := (h (s-1) (s-1) hsi hsi hsp hsp).2
  rw [hs1] at hone
  have honeT : R.T s s = 1 := by omega
  have others : ∀ j, 1 ≤ j → j ≤ n → j ≠ s → R.T j j + R.xi j j = 0 := by
    intro j hj hjn hjs
    by_contra hn
    have hji : j - 1 ∈ Finset.range n := by simp; omega
    have hj1 : j - 1 + 1 = j := by omega
    have ho := (h (s-1) (j-1) hsi hji hsp (by simpa [hj1] using hn)).1
    omega
  refine ⟨honeT, ?_, ?_⟩
  · intro j hj hjn
    by_cases hjs : j = s
    · simpa [hjs] using honeT
    · have ho := others j hj hjn hjs
      simp only [ite_eq_right hjs]
      omega
  · intro j hj hjn
    by_cases hjs : j = s
    · subst j; omega
    · have ho := others j hj hjn hjs
      omega

lemma anchor_run (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) (hpos : 0 < R.T s s)
    (i : ℕ) (hi : i ≤ n) : R.u 1 i = if 0 < i ∧ i < s then 1 else 0 := by
  obtain ⟨_, ht, hx⟩ := R.unique_start s hs hsn hpos
  induction i with
  | zero => simp [R.u_out 1 0 (by omega)]
  | succ i ih =>
    have hp := ih (by omega)
    have hst := R.start (i+1) (by omega) hi
    rw [ht (i+1) (by omega) hi, hx (i+1) (by omega) hi] at hst
    simp only [Nat.add_sub_cancel, add_zero] at hst
    split_ifs at hp hst ⊢ <;> omega

lemma other_rows_zero (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hpos : 0 < R.T s s) (j i : ℕ) (hjs : j ≠ s) : R.T j i = 0 := by
  by_cases hv : 1 ≤ j ∧ j ≤ i ∧ i ≤ n
  · have h := R.row_le_start j i hv.1 hv.2.1 hv.2.2
    have h0 := (R.unique_start s hs hsn hpos).2.1 j hv.1 (by omega)
    rw [ite_eq_right hjs] at h0
    omega
  · exact R.T_out j i hv

lemma diagonal_sum (j i t : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
    R.u j i = (∑ k ∈ Finset.range t, R.T (j+k) (i+k)) + R.u (j+t) (i+t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have hd := R.diagonal_all (j+t) (i+t) (by omega) (by omega)
    rw [hd] at ih
    simpa only [Nat.add_assoc] using ih

lemma u_one_row (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) (hpos : 0 < R.T s s)
    (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
    R.u j i = if j ≤ s then R.T s (i+s-j) else 0 := by
  have hsum := R.diagonal_sum j i (n+1) hj hji
  rw [R.u_out (j+(n+1)) (i+(n+1)) (by omega), add_zero] at hsum
  rw [hsum]
  by_cases hjs : j ≤ s
  · rw [ite_eq_left hjs]
    rw [Finset.sum_eq_single (s-j)]
    · congr 1 <;> omega
    · intro k hk hks
      exact R.other_rows_zero s hs hsn hpos (j+k) (i+k) (by omega)
    · intro hk
      simp only [Finset.mem_range] at hk
      omega
  · rw [ite_eq_right hjs]
    apply Finset.sum_eq_zero
    intro k hk
    exact R.other_rows_zero s hs hsn hpos (j+k) (i+k) (by omega)

lemma row_formula (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) (hpos : 0 < R.T s s)
    (i : ℕ) (hsi : s ≤ i) (hi : i ≤ n) :
    R.T s i = if i + 1 < 2*s then 1 else 0 := by
  have hd := R.u_one_row s hs hsn hpos 1 (i+1-s) (by omega) (by omega)
  rw [ite_eq_left hs] at hd
  have he : i+1-s+s-1 = i := by omega
  rw [he] at hd
  rw [← hd, R.anchor_run s hs hsn hpos (i+1-s) (by omega)]
  split_ifs <;> omega

lemma xi_zero_before (s : ℕ) (hs : 1 ≤ s) (hsn : s ≤ n) (hpos : 0 < R.T s s)
    (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : i ≤ n) (hbefore : i+1 < 2*s) :
    R.xi j i = 0 := by
  by_cases hji' : j = i
  · subst i
    exact (R.unique_start s hs hsn hpos).2.2 j hj hi
  · have hr := R.row j (i-1) hj (by omega) (by omega)
    have he : i-1+1 = i := by omega
    rw [he] at hr
    by_cases hjs : j = s
    · subst j
      rw [R.row_formula s hs hsn hpos i hji hi,
        R.row_formula s hs hsn hpos (i-1) (by omega) (by omega),
        ite_eq_left hbefore, ite_eq_left (by omega)] at hr
      omega
    · rw [R.other_rows_zero s hs hsn hpos j i hjs,
        R.other_rows_zero s hs hsn hpos j (i-1) hjs] at hr
      omega

theorem positive_gap_zero_pairings (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hi : i ≤ n) (hu : 0 < R.u j i) :
    ∀ k, 1 ≤ k → k ≤ i → R.xi k i = 0 := by
  have hsum := R.diagonal_sum j i (n+1) hj hji
  rw [R.u_out (j+(n+1)) (i+(n+1)) (by omega), add_zero] at hsum
  have hp : 0 < ∑ k ∈ Finset.range (n+1), R.T (j+k) (i+k) := by omega
  obtain ⟨k, hk, htk⟩ := (Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hp
  have hv : 1 ≤ j+k ∧ j+k ≤ i+k ∧ i+k ≤ n := by
    by_contra hn
    rw [R.T_out (j+k) (i+k) hn] at htk
    omega
  let s := j+k
  have hs : 1 ≤ s := hv.1
  have hsn : s ≤ n := by dsimp [s]; omega
  have hpos : 0 < R.T s s := by
    have hl := R.row_le_start (j+k) (i+k) hv.1 hv.2.1 hv.2.2
    dsimp [s]; omega
  have hur := R.u_one_row s hs hsn hpos j i hj hji
  have hjs : j ≤ s := by dsimp [s]; omega
  rw [ite_eq_left hjs] at hur
  have htarget : i+s-j ≤ n := by
    by_contra hn
    rw [R.T_out s (i+s-j) (by omega)] at hur
    omega
  have hf := R.row_formula s hs hsn hpos (i+s-j) (by omega) htarget
  have hbefore : i+1 < 2*s := by
    rw [hur] at hu
    split_ifs at hf <;> omega
  intro k hk hki
  exact R.xi_zero_before s hs hsn hpos k i hk hki hi hbefore

end Recurrence

structure IntegerGaps (n : ℕ) where
  u : ℕ → ℕ → ℤ
  xi : ℕ → ℕ → ℤ
  u_out : ∀ j i, ¬(1 ≤ j ∧ j ≤ i ∧ i ≤ n) → u j i = 0
  u_nonneg : ∀ j i, 0 ≤ u j i
  xi_nonneg : ∀ j i, 1 ≤ j → j ≤ i → i ≤ n → 0 ≤ xi j i
  pairing : ∀ j i, 1 ≤ j → j ≤ i → i ≤ n →
    xi j i = (if i = 1 then 1 else 0) - u j i -
      (if j < i then u (j+1) i else u 1 i) +
      (if j < i then u j (i-1) else u 1 (j-1)) + u (j+1) (i+1)

namespace IntegerGaps
variable {n : ℕ} (A : IntegerGaps n)

def t (j i : ℕ) : ℤ := A.u j i - A.u (j+1) (i+1)

lemma t_row (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : i < n) :
    A.t j (i+1) + A.xi j (i+1) = A.t j i := by
  have h := A.pairing j (i+1) hj (by omega) (by omega)
  rw [ite_eq_right (show i+1 ≠ 1 by omega), ite_eq_left (by omega), ite_eq_left (by omega)] at h
  simp only [Nat.add_sub_cancel] at h
  dsimp [t]
  linarith

lemma t_start (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    A.t j j + A.xi j j + A.u 1 j = (if j = 1 then 1 else 0) + A.u 1 (j-1) := by
  have h := A.pairing j j hj le_rfl hjn
  simp only [lt_self_iff_false, ite_false] at h
  dsimp [t]
  linarith

lemma t_nonneg (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : i ≤ n) :
    0 ≤ A.t j i := by
  apply Nat.decreasingInduction' (m := i) (n := n) (P := fun k => 0 ≤ A.t j k) _ hi
  · dsimp [t]
    rw [A.u_out (j+1) (n+1) (by omega), sub_zero]
    exact A.u_nonneg j n
  · intro k hk hik hnext
    have hr := A.t_row j k hj (by omega) hk
    have hx := A.xi_nonneg j (k+1) hj (by omega) (by omega)
    linarith

def recurrence : Recurrence n where
  u j i := (A.u j i).toNat
  T j i := if 1 ≤ j ∧ j ≤ i ∧ i ≤ n then (A.t j i).toNat else 0
  xi j i := (A.xi j i).toNat
  u_out j i h := by simp only [A.u_out j i h, Int.toNat_zero]
  T_out j i h := by simp only [ite_eq_right h]
  diagonal j i hj hji hi := by
    rw [ite_eq_left ⟨hj, hji, hi⟩, ← Int.toNat_add (A.t_nonneg j i hj hji hi) (A.u_nonneg _ _)]
    congr 1
    dsimp [t]
    ring
  row j i hj hji hi := by
    rw [ite_eq_left ⟨hj, by omega, by omega⟩, ite_eq_left ⟨hj, hji, by omega⟩,
      ← Int.toNat_add (A.t_nonneg j (i+1) hj (by omega) (by omega))
        (A.xi_nonneg j (i+1) hj (by omega) (by omega)), A.t_row j i hj hji hi]
  start j hj hjn := by
    rw [ite_eq_left ⟨hj, le_rfl, hjn⟩,
      ← Int.toNat_add (A.t_nonneg j j hj le_rfl hjn) (A.xi_nonneg j j hj le_rfl hjn),
      ← Int.toNat_add (add_nonneg (A.t_nonneg j j hj le_rfl hjn)
        (A.xi_nonneg j j hj le_rfl hjn)) (A.u_nonneg 1 j), A.t_start j hj hjn]
    split_ifs <;> simp [Int.toNat_add, A.u_nonneg]

 theorem positive_gap_zero_pairings (j i : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hi : i ≤ n) (hu : 0 < A.u j i) :
    ∀ k, 1 ≤ k → k ≤ i → A.xi k i = 0 := by
  have hpos : 0 < A.recurrence.u j i := by
    change 0 < (A.u j i).toNat
    omega
  have h := A.recurrence.positive_gap_zero_pairings j i hj hji hi hpos
  intro k hk hki
  have hz := h k hk hki
  change (A.xi k i).toNat = 0 at hz
  have hn := A.xi_nonneg k i hk hki hi
  omega

end IntegerGaps
end ElementaryPositivity.TriangularGaps

end

end OAI
