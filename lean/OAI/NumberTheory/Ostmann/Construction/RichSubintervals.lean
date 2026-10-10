import OAI.NumberTheory.Ostmann.Arithmetic.WeightedIntervalMass

namespace OAI

/-! # Every sufficiently long subinterval of a rich grid is rich -/

namespace Ostmann

open scoped BigOperators

private theorem grid_increment_lower (f : ℕ → ℝ) (M : ℕ) (c : ℝ)
    (hstep : ∀ i < M, c ≤ f (i + 1) - f i) (j l : ℕ) (hjl : j ≤ l) (hl : l ≤ M) :
    ((l - j : ℕ) : ℝ) * c ≤ f l - f j := by
  have hiter : ∀ n : ℕ, j + n ≤ M → (n : ℝ) * c ≤ f (j + n) - f j := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hi := ih (by omega)
      have hs := hstep (j + n) (by omega)
      rw [Nat.cast_succ]
      have he : j + (n + 1) = j + n + 1 := by omega
      rw [he]
      linarith
  simpa only [Nat.add_sub_of_le hjl] using hiter (l - j) (by omega)

/-- A monotone cumulative mass whose grid cells have density at least `d`
has density at least `d/2` on each internal interval at least four cells long. -/
theorem rich_grid_subinterval (φ : ℝ → ℝ) (hmono : Monotone φ)
    (M : ℕ) (a h d : ℝ) (hh : 0 < h) (hd : 0 ≤ d)
    (hstep : ∀ i : ℕ, i < M →
      d * h ≤ φ (a + ((i : ℝ) + 1) * h) - φ (a + (i : ℝ) * h))
    (u v : ℝ) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ a + M * h)
    (hlong : 4 * h ≤ v - u) :
    (d / 2) * (v - u) ≤ φ v - φ u := by
  let j := ⌈(u - a) / h⌉₊
  let l := ⌊(v - a) / h⌋₊
  have hu0 : 0 ≤ (u - a) / h := div_nonneg (sub_nonneg.mpr hau) hh.le
  have hv0 : 0 ≤ (v - a) / h := div_nonneg (sub_nonneg.mpr (hau.trans huv)) hh.le
  have huj : u ≤ a + (j : ℝ) * h := by
    have hs := (div_le_iff₀ hh).mp (Nat.le_ceil ((u - a) / h))
    linarith
  have hju : a + (j : ℝ) * h < u + h := by
    have hs := mul_lt_mul_of_pos_right (Nat.ceil_lt_add_one hu0) hh
    have he : ((u - a) / h + 1) * h = u - a + h := by field_simp
    rw [he] at hs
    linarith
  have hlv : a + (l : ℝ) * h ≤ v := by
    have hs := (le_div_iff₀ hh).mp (Nat.floor_le hv0)
    linarith
  have hvl : v < a + ((l : ℝ) + 1) * h := by
    have hs := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one ((v - a) / h))
    linarith
  have hjl : j ≤ l := by
    by_contra! hbad
    have hbad' : (l : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_iff.mpr hbad)
    nlinarith
  have hlM : l ≤ M := by
    have hle : (l : ℝ) ≤ M := by nlinarith
    exact_mod_cast hle
  have hgrid := grid_increment_lower (fun i => φ (a + (i : ℝ) * h)) M (d * h)
    (by intro i hi; simpa only [Nat.cast_add, Nat.cast_one] using hstep i hi) j l hjl hlM
  rw [Nat.cast_sub hjl] at hgrid
  have hgap : (v - u) / 2 ≤ ((l : ℝ) - j) * h := by nlinarith
  have hmass : φ (a + (l : ℝ) * h) - φ (a + (j : ℝ) * h) ≤ φ v - φ u := by
    have hu := hmono huj
    have hv := hmono hlv
    linarith
  have hprod := mul_le_mul_of_nonneg_left hgap hd
  nlinarith

/-- A uniform unit-interval mass bound gives a linear bound, with just one
boundary interval of overhead. -/
theorem cdf_interval_upper (φ : ℝ → ℝ) (hmono : Monotone φ)
    (a₀ A : ℝ) (hA : 0 ≤ A)
    (hunit : ∀ a, a₀ ≤ a → φ (a + 1) - φ a ≤ A)
    (a b : ℝ) (ha : a₀ ≤ a) (hab : a ≤ b) :
    φ b - φ a ≤ A * (b - a + 1) := by
  let N := ⌈b - a⌉₊
  have hN : b ≤ a + (N : ℝ) := by have := Nat.le_ceil (b - a); linarith
  have hNup : (N : ℝ) < b - a + 1 := Nat.ceil_lt_add_one (sub_nonneg.mpr hab)
  have hsum := grid_increment_lower (fun i => -φ (a + (i : ℝ))) N (-A)
    (by
      intro i _
      have h := hunit (a + i) (ha.trans (le_add_of_nonneg_right (Nat.cast_nonneg _)))
      push_cast
      rw [add_assoc] at h
      linarith) 0 N (Nat.zero_le _) le_rfl
  simp only [Nat.sub_zero, Nat.cast_zero, add_zero] at hsum
  have hmono' := hmono hN
  nlinarith

/-- A long interval of positive density contains a whole block of any
prescribed fixed length with at least half that density. The only loss is
the final incomplete block. -/
theorem exists_dense_fixed_block (φ : ℝ → ℝ) (a L B d A : ℝ)
    (hL : 0 ≤ L) (hB : 0 < B) (hd : 0 < d) (hA : 0 ≤ A)
    (hupper : ∀ u v, a ≤ u → u ≤ v → v ≤ a + L →
      φ v - φ u ≤ A * (v - u + 1))
    (hroot : d * L ≤ φ (a + L) - φ a)
    (hlarge : 2 * A * (B + 1) < d * L) :
    ∃ b, a ≤ b ∧ b + B ≤ a + L ∧ (d / 2) * B ≤ φ (b + B) - φ b := by
  let N := ⌊L / B⌋₊
  have hNB : (N : ℝ) * B ≤ L :=
    (le_div_iff₀ hB).mp (Nat.floor_le (div_nonneg hL hB.le))
  have hLN : L < ((N : ℝ) + 1) * B :=
    (div_lt_iff₀ hB).mp (Nat.lt_floor_add_one (L / B))
  have htail := hupper (a + N * B) (a + L)
    (le_add_of_nonneg_right (by positivity)) (by linarith) le_rfl
  have hsum : (∑ i ∈ Finset.range N,
      (φ (a + ((i : ℝ) + 1) * B) - φ (a + (i : ℝ) * B))) =
        φ (a + N * B) - φ a := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] using
      Finset.sum_range_sub (fun i : ℕ => φ (a + (i : ℝ) * B)) N
  have hfull : (d / 2) * L < φ (a + N * B) - φ a := by nlinarith
  have hex : ∃ i ∈ Finset.range N,
      (d / 2) * B ≤ φ (a + ((i : ℝ) + 1) * B) - φ (a + (i : ℝ) * B) := by
    by_contra! hn
    have hs := Finset.sum_le_sum (fun i hi => (hn i hi).le)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
    rw [hsum] at hs
    nlinarith
  obtain ⟨i, hi, hdense⟩ := hex
  have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hi
  have hlast := mul_le_mul_of_nonneg_right hiN hB.le
  refine ⟨a + (i : ℝ) * B, le_add_of_nonneg_right (by positivity), by linarith, ?_⟩
  simpa only [add_mul, one_mul, add_assoc] using hdense

theorem rich_interval_node_subinterval {M : ℕ} (hM : 0 < M)
    (φ : ℝ → ℝ) (hmono : Monotone φ) (a L d : ℝ) (hL : 0 < L) (hd : 0 ≤ d)
    (w : List (Fin M))
    (hrich : ∀ i, d ≤ intervalNodeDensity φ a L (w ++ [i]))
    (u v : ℝ) (hu : (intervalNode a L w).1 ≤ u) (huv : u ≤ v)
    (hv : v ≤ (intervalNode a L w).1 + (intervalNode a L w).2)
    (hlong : 4 * ((intervalNode a L w).2 / M) ≤ v - u) :
    (d / 2) * (v - u) ≤ φ v - φ u := by
  have hW := intervalNode_width_pos hM a L hL w
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hh := div_pos hW hMr
  apply rich_grid_subinterval φ hmono M (intervalNode a L w).1
    ((intervalNode a L w).2 / M) d hh hd
  · intro i hi
    have hr := hrich ⟨i, hi⟩
    simp only [intervalNodeDensity, intervalNode_child] at hr
    have hr := (le_div_iff₀ hh).mp hr
    simpa only [add_mul, one_mul, add_assoc] using hr
  · exact hu
  · exact huv
  · have he : (M : ℝ) * ((intervalNode a L w).2 / M) = (intervalNode a L w).2 := by
      field_simp
    rwa [he]
  · exact hlong

end Ostmann

end OAI
