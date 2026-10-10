import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RationalPhaseSpacing

/-- A reduced rational approximation with error at most `q⁻²` separates
frequencies whose index difference has absolute value at most `q/2`.
The estimate is uniform over every possible nearest integer. -/
theorem separation_of_rational_approximation
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (h : ℤ) (hne : h ≠ 0) (hsmall : 2 * |h| ≤ (q : ℤ)) (k : ℤ) :
    1 / (2 * (q : ℝ)) ≤ |α * (h : ℝ) - k| := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhpos : (0 : ℤ) < |h| := abs_pos.mpr hne
  have hnotdvd : ¬ (q : ℤ) ∣ h := by
    intro hd
    have hle := Int.le_of_dvd hhpos ((dvd_abs (q : ℤ) h).mpr hd)
    omega
  have hnonzero : a * h - k * (q : ℤ) ≠ 0 := by
    intro hz
    apply hnotdvd
    apply hcop.symm.dvd_of_dvd_mul_left
    refine ⟨k, ?_⟩
    linear_combination hz
  have hinteger : (1 : ℝ) ≤ |(a : ℝ) * h - (k : ℝ) * q| := by
    exact_mod_cast Int.one_le_abs hnonzero
  have hsmallR : (2 : ℝ) * |(h : ℝ)| ≤ q := by exact_mod_cast hsmall
  have herr : (q : ℝ) * |α - (a : ℝ) / q| * |(h : ℝ)| ≤ 1 / 2 := by
    have hb := (le_div_iff₀ (sq_pos_of_pos hqR)).mp happrox
    have hc := mul_le_mul_of_nonneg_left hsmallR
      (mul_nonneg hqR.le (abs_nonneg (α - (a : ℝ) / q)))
    nlinarith
  have hid : (a : ℝ) * h - (k : ℝ) * q =
      (q : ℝ) * (α * h - k) - (q : ℝ) * (α - (a : ℝ) / q) * h := by
    field_simp
    ring
  have htri : |(a : ℝ) * h - (k : ℝ) * q| ≤
      (q : ℝ) * |α * h - k| + (q : ℝ) * |α - (a : ℝ) / q| * |(h : ℝ)| := by
    rw [hid]
    calc
      _ ≤ |(q : ℝ) * (α * h - k)| + |(q : ℝ) * (α - (a : ℝ) / q) * h| :=
        abs_sub _ _
      _ = _ := by simp only [abs_mul, abs_of_pos hqR]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
  nlinarith

/-- Fractional parts at two nearby distinct integer indices are separated
under the same reduced rational approximation. -/
theorem fract_separation
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (m n : ℤ) (hne : m ≠ n) (hsmall : 2 * |m - n| ≤ (q : ℤ)) :
    1 / (2 * (q : ℝ)) ≤ |Int.fract (α * m) - Int.fract (α * n)| := by
  have hs := separation_of_rational_approximation α a q hq hcop happrox
    (m - n) (sub_ne_zero.mpr hne) hsmall (⌊α * m⌋ - ⌊α * n⌋)
  simpa only [Int.fract, Int.cast_sub, mul_sub, sub_sub_sub_comm] using hs

/-- The fractional parts of a short block occupy each interval of length
`1/(2q)` at most once. Half-open endpoints are important at exact spacing. -/
theorem card_fract_interval_le_one
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (A : Finset ℤ) (hspan : ∀ m ∈ A, ∀ n ∈ A, 2 * |m - n| ≤ (q : ℤ))
    (b : ℝ) :
    (A.filter (fun n : ℤ => b ≤ Int.fract (α * (n : ℝ)) ∧
      Int.fract (α * (n : ℝ)) < b + 1 / (2 * (q : ℝ)))).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro m hm n hn
  obtain ⟨hmA, hmlow, hmhigh⟩ := Finset.mem_filter.mp hm
  obtain ⟨hnA, hnlow, hnhigh⟩ := Finset.mem_filter.mp hn
  by_contra hne
  have hs := fract_separation α a q hq hcop happrox m n hne (hspan m hmA n hnA)
  have hlt : |Int.fract (α * m) - Int.fract (α * n)| < 1 / (2 * (q : ℝ)) := by
    apply abs_sub_lt_iff.mpr
    constructor <;> linarith
  exact (not_lt_of_ge hs) hlt

/-- A canonical finite bin index for the phase of an integer. -/
def phaseBin (q : ℕ) (α : ℝ) (n : ℤ) : ℕ :=
  ⌊2 * (q : ℝ) * Int.fract (α * n)⌋₊

theorem phaseBin_lt (q : ℕ) (hq : 0 < q) (α : ℝ) (n : ℤ) :
    phaseBin q α n < 2 * q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply (Nat.floor_lt (mul_nonneg (by positivity) (Int.fract_nonneg (α * (n : ℝ))))).mpr
  push_cast
  nlinarith [Int.fract_lt_one (α * n)]

/-- Bin encoding preserves the multiplicity of indices in every short block:
no two indices have the same bin. -/
theorem phaseBin_injOn
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (A : Finset ℤ) (hspan : ∀ m ∈ A, ∀ n ∈ A, 2 * |m - n| ≤ (q : ℤ)) :
    Set.InjOn (phaseBin q α) A := by
  intro m hm n hn heq
  by_contra hne
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hs := fract_separation α a q hq hcop happrox m n hne (hspan m hm n hn)
  have hmlo := Nat.floor_le (show 0 ≤ 2 * (q : ℝ) * Int.fract (α * m) from mul_nonneg (by positivity) (Int.fract_nonneg _))
  have hnlo := Nat.floor_le (show 0 ≤ 2 * (q : ℝ) * Int.fract (α * n) from mul_nonneg (by positivity) (Int.fract_nonneg _))
  have hmhi := Nat.lt_floor_add_one (2 * (q : ℝ) * Int.fract (α * m))
  have hnhi := Nat.lt_floor_add_one (2 * (q : ℝ) * Int.fract (α * n))
  change phaseBin q α m = phaseBin q α n at heq
  change (phaseBin q α m : ℝ) ≤ _ at hmlo
  change (phaseBin q α n : ℝ) ≤ _ at hnlo
  change _ < (phaseBin q α m : ℝ) + 1 at hmhi
  change _ < (phaseBin q α n : ℝ) + 1 at hnhi
  rw [heq] at hmlo hmhi
  have hlt : |Int.fract (α * m) - Int.fract (α * n)| < 1 / (2 * (q : ℝ)) := by
    apply abs_sub_lt_iff.mpr
    constructor
    · apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
      nlinarith
    · apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
      nlinarith
  exact (not_lt_of_ge hs) hlt

/-- A reciprocal truncated at `Y`, with its correct value at the singular
point. The special value is needed for geometric exponential sums. -/
def truncatedInv (Y x : ℝ) : ℝ := if x = 0 then Y else min Y (1 / x)

theorem truncatedInv_nonneg {Y x : ℝ} (hY : 0 ≤ Y) (hx : 0 ≤ x) :
    0 ≤ truncatedInv Y x := by
  unfold truncatedInv
  split_ifs
  · exact hY
  · exact le_min hY (one_div_nonneg.mpr hx)

theorem truncatedInv_le_cap (Y x : ℝ) : truncatedInv Y x ≤ Y := by
  unfold truncatedInv
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- Bin majorant for the one-sided reciprocal distance. -/
def binWeight (H : ℕ) (Y : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then Y else (H : ℝ) / j

theorem binWeight_nonneg {H j : ℕ} {Y : ℝ} (hY : 0 ≤ Y) :
    0 ≤ binWeight H Y j := by
  unfold binWeight
  split_ifs
  · exact hY
  · positivity

theorem truncatedInv_fract_le_binWeight (q : ℕ) (hq : 0 < q)
    (Y α : ℝ) (n : ℤ) :
    truncatedInv Y (Int.fract (α * n)) ≤ binWeight (2 * q) Y (phaseBin q α n) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hj : phaseBin q α n = 0
  · simpa [binWeight, hj] using truncatedInv_le_cap Y (Int.fract (α * n))
  · have hjpos : (0 : ℝ) < phaseBin q α n := by exact_mod_cast Nat.pos_of_ne_zero hj
    have hlo := Nat.floor_le (show 0 ≤ 2 * (q : ℝ) * Int.fract (α * n)
      from mul_nonneg (by positivity) (Int.fract_nonneg _))
    change (phaseBin q α n : ℝ) ≤ _ at hlo
    have hxpos : 0 < Int.fract (α * n) := by nlinarith [Int.fract_nonneg (α * (n : ℝ))]
    rw [binWeight, ite_eq_right hj, truncatedInv, ite_eq_right (ne_of_gt hxpos)]
    apply (min_le_right _ _).trans
    apply (div_le_div_iff₀ hxpos hjpos).mpr
    push_cast
    simpa using hlo

/-- Summing the bin majorants costs one singular term and a harmonic sum. -/
theorem sum_binWeight_le (H : ℕ) (hH : 0 < H) (Y : ℝ) :
    (∑ j ∈ Finset.range H, binWeight H Y j) ≤
      Y + (H : ℝ) * (1 + Real.log (H : ℝ)) := by
  have hterm (j : ℕ) : binWeight H Y j =
      (if j = 0 then Y else 0) + (H : ℝ) * (1 / (j : ℝ)) := by
    by_cases hj : j = 0
    · simp [binWeight, hj]
    · simp [binWeight, hj, div_eq_mul_inv]
  have hsum : (∑ j ∈ Finset.range H, binWeight H Y j) =
      Y + (H : ℝ) * ∑ j ∈ Finset.range H, (1 / (j : ℝ)) := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [hH]
  have hrecip : (∑ j ∈ Finset.range H, (1 / (j : ℝ))) ≤ (harmonic H : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (H + 1), (1 / (j : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        intro j _ _
        positivity
      _ = (harmonic H : ℝ) := by
        rw [Finset.sum_range_succ']
        simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [hsum]
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left (hrecip.trans (harmonic_le_one_add_log H)) (Nat.cast_nonneg H)

/-- A reduced rational approximation controls the sum of truncated one-sided
reciprocal distances on every short block. No cancellation hypothesis is used. -/
theorem sum_truncatedInv_fract_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (A : Finset ℤ) (hspan : ∀ m ∈ A, ∀ n ∈ A, 2 * |m - n| ≤ (q : ℤ))
    (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ A, truncatedInv Y (Int.fract (α * n))) ≤
      Y + (2 * (q : ℝ)) * (1 + Real.log (2 * (q : ℝ))) := by
  classical
  have hinj := phaseBin_injOn α a q hq hcop happrox A hspan
  calc
    _ ≤ ∑ n ∈ A, binWeight (2 * q) Y (phaseBin q α n) := by
      exact Finset.sum_le_sum (fun n _ => truncatedInv_fract_le_binWeight q hq Y α n)
    _ = ∑ j ∈ A.image (phaseBin q α), binWeight (2 * q) Y j := by
      rw [Finset.sum_image]
      exact fun m hm n hn heq => hinj hm hn heq
    _ ≤ ∑ j ∈ Finset.range (2 * q), binWeight (2 * q) Y j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_range.mpr (phaseBin_lt q hq α n)
      · intro j _ _
        exact binWeight_nonneg hY
    _ ≤ _ := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using sum_binWeight_le (2 * q) (by omega) Y

/-- Distance of a real phase to the nearest integer, expressed without a
choice of nearest integer. -/
def intDistance (x : ℝ) : ℝ := min (Int.fract x) (1 - Int.fract x)

@[simp] theorem intDistance_eq_abs_sub_round (x : ℝ) :
    intDistance x = |x - round x| := (abs_sub_round_eq_min x).symm

theorem intDistance_nonneg (x : ℝ) : 0 ≤ intDistance x :=
  le_min (Int.fract_nonneg x) (sub_nonneg.mpr (Int.fract_lt_one x).le)

/-- Two one-sided reciprocal majorants control the nearest-integer one,
including integer phases where the truncation must equal `Y`. -/
theorem truncatedInv_intDistance_le {Y : ℝ} (hY : 0 ≤ Y) (x : ℝ) :
    truncatedInv Y (intDistance x) ≤
      truncatedInv Y (Int.fract x) + truncatedInv Y (Int.fract (-x)) := by
  have hsecond : truncatedInv Y (1 - Int.fract x) ≤ truncatedInv Y (Int.fract (-x)) := by
    by_cases hx : Int.fract x = 0
    · have hneg := Int.fract_neg_eq_zero.mpr hx
      rw [hneg]
      simpa [truncatedInv] using truncatedInv_le_cap Y (1 - Int.fract x)
    · rw [Int.fract_neg hx]
  unfold intDistance
  rcases le_total (Int.fract x) (1 - Int.fract x) with h | h
  · rw [min_eq_left h]
    exact le_add_of_nonneg_right (truncatedInv_nonneg hY (Int.fract_nonneg _))
  · rw [min_eq_right h]
    exact hsecond.trans (le_add_of_nonneg_left (truncatedInv_nonneg hY (Int.fract_nonneg _)))

/-- The classical truncated reciprocal-distance estimate on one short block,
with an explicit constant and correct treatment of integer phases. -/
theorem sum_truncatedInv_intDistance_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (A : Finset ℤ) (hspan : ∀ m ∈ A, ∀ n ∈ A, 2 * |m - n| ≤ (q : ℤ))
    (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ A, truncatedInv Y (intDistance (α * n))) ≤
      2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))) := by
  have hnegative : |(-α) - ((-a : ℤ) : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
    simpa only [Int.cast_neg, neg_div, neg_sub_neg, abs_sub_comm] using happrox
  have hp := sum_truncatedInv_fract_le α a q hq hcop happrox A hspan Y hY
  have hn := sum_truncatedInv_fract_le (-α) (-a) q hq hcop.neg_left hnegative A hspan Y hY
  have hs : (∑ n ∈ A, truncatedInv Y (intDistance (α * n))) ≤
      (∑ n ∈ A, truncatedInv Y (Int.fract (α * n))) +
        ∑ n ∈ A, truncatedInv Y (Int.fract ((-α) * n)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n _
    simpa only [neg_mul] using truncatedInv_intDistance_le hY (α * n)
  linarith

/-- Any interval of `floor(q/2)+1` consecutive integers is a short block. -/
theorem short_interval_span (q : ℕ) (L : ℤ) :
    ∀ m ∈ Finset.Ico L (L + (q / 2 : ℕ) + 1),
      ∀ n ∈ Finset.Ico L (L + (q / 2 : ℕ) + 1),
        2 * |m - n| ≤ (q : ℤ) := by
  intro m hm n hn
  have hm' := Finset.mem_Ico.mp hm
  have hn' := Finset.mem_Ico.mp hn
  have hh : 2 * (q / 2 : ℕ) ≤ q := by omega
  have hh' : (2 : ℤ) * (q / 2 : ℕ) ≤ q := by exact_mod_cast hh
  have habs : |m - n| ≤ (q / 2 : ℕ) := by
    apply abs_le.mpr
    constructor <;> omega
  omega

/-- Interval form of the short-block estimate used in Type I/II decompositions. -/
theorem sum_truncatedInv_intDistance_short_interval_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ Finset.Ico L (L + (q / 2 : ℕ) + 1), truncatedInv Y (intDistance (α * n))) ≤
      2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))) :=
  sum_truncatedInv_intDistance_le α a q hq hcop happrox _ (short_interval_span q L) Y hY

theorem sum_int_Ico_add (f : ℤ → ℝ) (L M R : ℤ)
    (hLM : L ≤ M) (hMR : M ≤ R) :
    (∑ n ∈ Finset.Ico L M, f n) + (∑ n ∈ Finset.Ico M R, f n) =
      ∑ n ∈ Finset.Ico L R, f n := by
  have hdisj : Disjoint (Finset.Ico L M) (Finset.Ico M R) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have h := Finset.mem_Ico.mp hn
    have h' := Finset.mem_Ico.mp hn'
    omega
  have hunion : Finset.Ico L M ∪ Finset.Ico M R = Finset.Ico L R := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  rw [← Finset.sum_union hdisj, hunion]

/-- Aggregate an estimate on consecutive blocks, with no periodicity premise. -/
theorem sum_int_Ico_le_blocks (f : ℤ → ℝ) (B : ℕ) (hB : 0 < B) (C : ℝ)
    (hblock : ∀ L : ℤ, (∑ n ∈ Finset.Ico L (L + B), f n) ≤ C)
    (L : ℤ) (k : ℕ) :
    (∑ n ∈ Finset.Ico L (L + (k : ℤ) * B), f n) ≤ (k : ℝ) * C := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hBz : (0 : ℤ) < B := by exact_mod_cast hB
    have hleft : L ≤ L + (k : ℤ) * B := le_add_of_nonneg_right (by positivity)
    have hright : L + (k : ℤ) * B ≤ L + (k : ℤ) * B + B := by omega
    have hend : L + ((k + 1 : ℕ) : ℤ) * B = L + (k : ℤ) * B + B := by
      push_cast
      ring
    rw [hend, ← sum_int_Ico_add f L (L + (k : ℤ) * B)
      (L + (k : ℤ) * B + B) hleft hright]
    calc
      _ ≤ (k : ℝ) * C + C := add_le_add ih (hblock (L + (k : ℤ) * B))
      _ = ((k + 1 : ℕ) : ℝ) * C := by push_cast; ring

/-- Full interval version, with the exact number of short blocks. -/
theorem sum_truncatedInv_intDistance_interval_le_blocks
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ Finset.Ico L (L + N), truncatedInv Y (intDistance (α * n))) ≤
      ((N / (q / 2 + 1) + 1 : ℕ) : ℝ) *
        (2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) := by
  let B : ℕ := q / 2 + 1
  have hB : 0 < B := by dsimp [B]; omega
  have hcover : N ≤ (N / B + 1) * B := by
    simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ N hB).le
  have hcoverZ : (N : ℤ) ≤ ((N / B + 1 : ℕ) : ℤ) * B := by exact_mod_cast hcover
  have hs := sum_int_Ico_le_blocks
    (fun n : ℤ => truncatedInv Y (intDistance (α * n))) B hB
    (2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ))))
    (fun l => by
      simpa [B, Nat.cast_add, Nat.cast_one, add_assoc] using
        sum_truncatedInv_intDistance_short_interval_le α a q hq hcop happrox l Y hY)
    L (N / B + 1)
  apply le_trans ?_ hs
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Ico_subset_Ico le_rfl (by omega)
  · intro n _ _
    exact truncatedInv_nonneg hY (intDistance_nonneg _)

/-- Standard convenient full-interval form of the rational approximation
reciprocal-distance estimate. It applies equally to negative interval origins. -/
theorem sum_truncatedInv_intDistance_interval_le
    (α : ℝ) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime a (q : ℤ))
    (happrox : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (L : ℤ) (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    (∑ n ∈ Finset.Ico L (L + N), truncatedInv Y (intDistance (α * n))) ≤
      (2 * (N : ℝ) / q + 1) *
        (2 * Y + 4 * (q : ℝ) * (1 + Real.log (2 * (q : ℝ)))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : q ≤ 2 * (q / 2 + 1) := by omega
  have hhR : (q : ℝ) ≤ 2 * ((q / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hh
  have hdivR : ((N / (q / 2 + 1) : ℕ) : ℝ) * ((q / 2 + 1 : ℕ) : ℝ) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N (q / 2 + 1)
  have hcount : ((N / (q / 2 + 1) + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) / q + 1 := by
    push_cast
    apply add_le_add _ le_rfl
    apply (le_div_iff₀ hqR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhR (Nat.cast_nonneg (N / (q / 2 + 1)) :
      (0 : ℝ) ≤ (N / (q / 2 + 1) : ℕ))]
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := by
    apply Real.log_nonneg
    have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  exact (sum_truncatedInv_intDistance_interval_le_blocks α a q hq hcop happrox L N Y hY).trans
    (mul_le_mul_of_nonneg_right hcount (by positivity))

end Problem337.RationalPhaseSpacing

end

end OAI
