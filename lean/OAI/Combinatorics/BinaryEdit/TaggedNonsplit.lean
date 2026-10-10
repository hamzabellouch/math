import Mathlib

namespace OAI

/-! Loss counting for nonsplit rows with a local row-pair matching bound. -/

namespace TreeEdit.BinaryLower.TaggedNonsplit

open scoped BigOperators

/-- Number of matched source positions assigned to a specified row. -/
def rowCount {N T : ℕ} (row : Fin N → Fin T) (r : Fin T) : ℕ :=
  (Finset.univ.filter fun i => row i = r).card

/-- Partition the matching by its source row. -/
theorem sum_rowCount {N T : ℕ} (row : Fin N → Fin T) :
    ∑ r, rowCount row r = N := by
  simpa [rowCount] using Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin N)) (Finset.univ : Finset (Fin T)) row

/-- An injective matching cannot use more than `W` positions in one row
of width `W`. The row indices are specified by Euclidean division. -/
theorem rowCount_le_width {N T W : ℕ}
    (u : Fin N → ℕ) (row : Fin N → Fin T)
    (hW : 0 < W) (hu : Function.Injective u)
    (hrow : ∀ i, u i / W = (row i).val) (r : Fin T) :
    rowCount row r ≤ W := by
  classical
  unfold rowCount
  calc
    (Finset.univ.filter fun i => row i = r).card ≤ (Finset.range W).card := by
      apply Finset.card_le_card_of_injOn (fun i => u i % W)
      · intro i _
        exact Finset.mem_range.mpr (Nat.mod_lt _ hW)
      · intro i hi j hj hmod
        have hir : row i = r := (Finset.mem_filter.mp hi).2
        have hjr : row j = r := (Finset.mem_filter.mp hj).2
        have hquot : u i / W = u j / W := by rw [hrow, hrow, hir, hjr]
        apply hu
        have hi' := Nat.mod_add_div (u i) W
        have hj' := Nat.mod_add_div (u j) W
        change u i % W = u j % W at hmod
        rw [hquot, hmod] at hi'
        omega
    _ = W := Finset.card_range W

/-- Sum the losses in nonsplit rows. The rows in `S` may have no local
loss estimate; the capacity bound alone makes their losses nonnegative. -/
theorem nonsplit_loss_bound {N T : ℕ} (row : Fin N → Fin T)
    (S : Finset (Fin T)) (W d : ℝ)
    (hcapacity : ∀ r, (rowCount row r : ℝ) ≤ W)
    (hnonsplit : ∀ r, r ∉ S → (rowCount row r : ℝ) ≤ W - d) :
    d * ((T : ℝ) - S.card) ≤ (T : ℝ) * W - N := by
  classical
  have hsum : (∑ r, (rowCount row r : ℝ)) = (N : ℝ) := by
    exact_mod_cast sum_rowCount row
  have hcard : (Sᶜ.card : ℝ) = (T : ℝ) - S.card := by
    rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub]
    simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hlow : (Sᶜ.card : ℝ) * d ≤
      ∑ r ∈ Sᶜ, (W - (rowCount row r : ℝ)) := by
    calc
      (Sᶜ.card : ℝ) * d = ∑ _r ∈ Sᶜ, d := by simp
      _ ≤ ∑ r ∈ Sᶜ, (W - (rowCount row r : ℝ)) := by
        apply Finset.sum_le_sum
        intro r hr
        have h := hnonsplit r (Finset.mem_compl.mp hr)
        linarith
  have hle : (∑ r ∈ Sᶜ, (W - (rowCount row r : ℝ))) ≤
      ∑ r, (W - (rowCount row r : ℝ)) :=
    Finset.sum_le_univ_sum_of_nonneg fun r => sub_nonneg.mpr (hcapacity r)
  have htotal : (∑ r, (W - (rowCount row r : ℝ))) = (T : ℝ) * W - N := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  rw [hcard] at hlow
  simpa only [mul_comm] using hlow.trans (hle.trans_eq htotal)

/-- Nonsplit tagged-row loss for an actual injective list of source positions. -/
theorem nonsplit_loss_bound_of_positions {N T W : ℕ}
    (u : Fin N → ℕ) (row : Fin N → Fin T)
    (S : Finset (Fin T)) (d : ℝ)
    (hW : 0 < W) (hu : Function.Injective u)
    (hrow : ∀ i, u i / W = (row i).val)
    (hnonsplit : ∀ r, r ∉ S → (rowCount row r : ℝ) ≤ (W : ℝ) - d) :
    d * ((T : ℝ) - S.card) ≤ (T : ℝ) * W - N := by
  apply nonsplit_loss_bound row S (W : ℝ) d
  · intro r
    exact_mod_cast rowCount_le_width u row hW hu hrow r
  · exact hnonsplit

/-- Matched positions in a specified source/target row pair. -/
def rowPairCount {N T U : ℕ} (row : Fin N → Fin T)
    (target : Fin N → Fin U) (r : Fin T) (b : Fin U) : ℕ :=
  (Finset.univ.filter fun i => row i = r ∧ target i = b).card

/-- In a nonsplit row with a match, every match belongs to the same row pair. -/
theorem rowCount_eq_rowPairCount {N T U : ℕ}
    (row : Fin N → Fin T) (target : Fin N → Fin U) (r : Fin T)
    (hconstant : ∀ i j, row i = r → row j = r → target i = target j)
    (i : Fin N) (hi : row i = r) :
    rowCount row r = rowPairCount row target r (target i) := by
  unfold rowCount rowPairCount
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hj => ⟨hj, hconstant j i hj hi⟩, fun hj => hj.1⟩

/-- Local row-pair bounds apply to a nonsplit row, including the case of a
row with no matches. The latter case uses the necessary bound `d≤W`. -/
theorem nonsplit_rowCount_le {N T U : ℕ}
    (row : Fin N → Fin T) (target : Fin N → Fin U) (r : Fin T)
    (W d : ℝ) (hdW : d ≤ W)
    (hconstant : ∀ i j, row i = r → row j = r → target i = target j)
    (hpair : ∀ b, (rowPairCount row target r b : ℝ) ≤ W - d) :
    (rowCount row r : ℝ) ≤ W - d := by
  classical
  by_cases hmatch : ∃ i, row i = r
  · obtain ⟨i, hi⟩ := hmatch
    rw [rowCount_eq_rowPairCount row target r hconstant i hi]
    exact hpair (target i)
  · have hzero : rowCount row r = 0 := by
      simp only [rowCount, Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hmatch ⟨i, (Finset.mem_filter.mp hi).2⟩
    rw [hzero, Nat.cast_zero]
    exact sub_nonneg.mpr hdW

/-- The source-loss estimate `E ≥ d(T-s)` from semantic nonsplitting and
local row-pair bounds. All finite matching positions, including an empty
matching and rows without matches, are covered. -/
theorem nonsplit_loss_of_pair_bounds {N T U W : ℕ}
    (u : Fin N → ℕ) (row : Fin N → Fin T) (target : Fin N → Fin U)
    (S : Finset (Fin T)) (d : ℝ)
    (hW : 0 < W) (hu : Function.Injective u)
    (hrow : ∀ i, u i / W = (row i).val) (hdW : d ≤ (W : ℝ))
    (hconstant : ∀ r, r ∉ S →
      ∀ i j, row i = r → row j = r → target i = target j)
    (hpair : ∀ r b, (rowPairCount row target r b : ℝ) ≤ (W : ℝ) - d) :
    d * ((T : ℝ) - S.card) ≤ (T : ℝ) * W - N := by
  apply nonsplit_loss_bound_of_positions u row S d hW hu hrow
  intro r hr
  exact nonsplit_rowCount_le row target r (W : ℝ) d hdW
    (hconstant r hr) (hpair r)

/-- Number of matches assigned to a natural row index. -/
def natRowCount {N : ℕ} (row : Fin N → ℕ) (r : ℕ) : ℕ :=
  (Finset.univ.filter fun i => row i = r).card

/-- Partition the matching by natural row indices in `[0,T)`. -/
theorem sum_natRowCount {N T : ℕ} (row : Fin N → ℕ)
    (hrow : ∀ i, row i < T) :
    ∑ r ∈ Finset.range T, natRowCount row r = N := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin N)) (Finset.range T) row
  simpa only [natRowCount, Finset.mem_range, hrow, Finset.filter_true,
    Finset.card_univ, Fintype.card_fin] using h

/-- Nonsplit summation with natural row indices, avoiding any conversion of
`splitRows` to a Fin-indexed set. -/
theorem nonsplit_loss_bound_nat {N T : ℕ} (row : Fin N → ℕ)
    (S : Finset ℕ) (W d : ℝ)
    (hrow : ∀ i, row i < T) (hS : S ⊆ Finset.range T)
    (hcapacity : ∀ r < T, (natRowCount row r : ℝ) ≤ W)
    (hnonsplit : ∀ r < T, r ∉ S → (natRowCount row r : ℝ) ≤ W - d) :
    d * ((T : ℝ) - S.card) ≤ (T : ℝ) * W - N := by
  classical
  let G := Finset.range T \ S
  have hsum : (∑ r ∈ Finset.range T, (natRowCount row r : ℝ)) = (N : ℝ) := by
    exact_mod_cast sum_natRowCount row hrow
  have hcard : (G.card : ℝ) = (T : ℝ) - S.card := by
    dsimp [G]
    rw [Finset.card_sdiff_of_subset hS, Finset.card_range, Nat.cast_sub]
    simpa using Finset.card_le_card hS
  have hlow : (G.card : ℝ) * d ≤
      ∑ r ∈ G, (W - (natRowCount row r : ℝ)) := by
    calc
      (G.card : ℝ) * d = ∑ _r ∈ G, d := by simp
      _ ≤ ∑ r ∈ G, (W - (natRowCount row r : ℝ)) := by
        apply Finset.sum_le_sum
        intro r hr
        obtain ⟨hrT, hrS⟩ := Finset.mem_sdiff.mp hr
        have h := hnonsplit r (Finset.mem_range.mp hrT) hrS
        linarith
  have hle : (∑ r ∈ G, (W - (natRowCount row r : ℝ))) ≤
      ∑ r ∈ Finset.range T, (W - (natRowCount row r : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    intro r hr _
    exact sub_nonneg.mpr (hcapacity r (Finset.mem_range.mp hr))
  have htotal : (∑ r ∈ Finset.range T, (W - (natRowCount row r : ℝ))) =
      (T : ℝ) * W - N := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  rw [hcard] at hlow
  simpa only [mul_comm] using hlow.trans (hle.trans_eq htotal)

/-- Capacity of one natural-indexed row under an injective source map. -/
theorem natRowCount_div_le_width {N : ℕ}
    (u : Fin N → ℕ) (hu : Function.Injective u) (W : ℕ) (hW : 0 < W) (r : ℕ) :
    natRowCount (fun i => u i / W) r ≤ W := by
  classical
  unfold natRowCount
  calc
    (Finset.univ.filter fun i => u i / W = r).card ≤ (Finset.range W).card := by
      apply Finset.card_le_card_of_injOn (fun i => u i % W)
      · intro i _
        exact Finset.mem_range.mpr (Nat.mod_lt _ hW)
      · intro i hi j hj hmod
        have hir : u i / W = r := (Finset.mem_filter.mp hi).2
        have hjr : u j / W = r := (Finset.mem_filter.mp hj).2
        apply hu
        have hi' := Nat.mod_add_div (u i) W
        have hj' := Nat.mod_add_div (u j) W
        change u i % W = u j % W at hmod
        rw [hir, hmod] at hi'
        rw [hjr] at hj'
        omega
    _ = W := Finset.card_range W

/-- Numeric nonsplit estimate with exactly the row convention `position/B/m`
and the natural unmatched count. -/
theorem nonsplit_loss_numeric {N T m B : ℕ}
    (u : Fin N → ℕ) (hu : Function.Injective u)
    (hm : 0 < m) (hB : 0 < B) (hub : ∀ i, u i < T * m * B)
    (S : Finset ℕ) (hS : S ⊆ Finset.range T) (d : ℝ)
    (hnonsplit : ∀ r < T, r ∉ S →
      ((Finset.univ.filter fun i => u i / B / m = r).card : ℝ) ≤
        (m * B : ℕ) - d) :
    d * ((T : ℝ) - S.card) ≤ ((T * m * B - N : ℕ) : ℝ) := by
  classical
  have hW : 0 < B * m := Nat.mul_pos hB hm
  have hub' : ∀ i, u i < T * (B * m) := by
    intro i
    simpa only [Nat.mul_comm B m, Nat.mul_assoc] using hub i
  have hrow : ∀ i, u i / B / m < T := by
    intro i
    rw [Nat.div_div_eq_div_mul]
    exact (Nat.div_lt_iff_lt_mul hW).mpr (hub' i)
  have hN : N ≤ T * m * B := by
    calc
      N = (Finset.univ : Finset (Fin N)).card := by simp
      _ ≤ (Finset.range (T * m * B)).card := by
        apply Finset.card_le_card_of_injOn u
        · intro i _
          exact Finset.mem_range.mpr (hub i)
        · exact fun i _ j _ hij => hu hij
      _ = T * m * B := Finset.card_range _
  have h := nonsplit_loss_bound_nat (fun i => u i / B / m) S (m * B : ℕ) d
    hrow hS (fun r _ => ?_) hnonsplit
  · rw [Nat.cast_sub hN]
    simpa only [Nat.cast_mul, mul_assoc] using h
  · have hc := natRowCount_div_le_width u hu (B * m) hW r
    rw [Nat.mul_comm B m] at hc
    simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm B m] using
      (Nat.cast_le.mpr hc : (natRowCount (fun i => u i / (m * B)) r : ℝ) ≤
        ((m * B : ℕ) : ℝ))

end TreeEdit.BinaryLower.TaggedNonsplit

end OAI
