import OAI.Combinatorics.ProgressionColoring.CyclicModel
import OAI.Combinatorics.ProgressionColoring.TernarySign
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Int.Interval

namespace OAI

namespace QuantitativeVanDerWaerden.UniformMesh

noncomputable section

/-- The left endpoint of a literal interval in `[0,1)`. -/
def left (n : ℕ) (i : Fin n) : ℝ := (i.val : ℝ) / n

/-- The upper endpoint is excluded. -/
def right (n : ℕ) (i : Fin n) : ℝ := ((i.val : ℝ) + 1) / n

def Contains (n : ℕ) (i : Fin n) (x : ℝ) : Prop :=
  left n i ≤ x ∧ x < right n i

def label (n : ℕ) (hn : 0 < n) (x : ℝ) : Fin n :=
  ⟨⌊(n : ℝ) * Int.fract x⌋₊, by
    apply (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg n) (Int.fract_nonneg x))).2
    have hp : (0 : ℝ) < n := by exact_mod_cast hn
    simpa only [mul_one] using mul_lt_mul_of_pos_left (Int.fract_lt_one x) hp⟩

@[simp] theorem label_val (n : ℕ) (hn : 0 < n) (x : ℝ) :
    (label n hn x).val = ⌊(n : ℝ) * Int.fract x⌋₊ := rfl

theorem left_nonneg (n : ℕ) (i : Fin n) : 0 ≤ left n i := by
  unfold left
  positivity

theorem right_le_one (n : ℕ) (hn : 0 < n) (i : Fin n) : right n i ≤ 1 := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_one hp).2
  exact_mod_cast (Nat.add_one_le_iff.mpr i.isLt)

theorem left_lt_right (n : ℕ) (hn : 0 < n) (i : Fin n) : left n i < right n i := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  exact (div_lt_div_iff_of_pos_right hp).2 (by linarith)

theorem width_eq (n : ℕ) (i : Fin n) : right n i - left n i = 1 / (n : ℝ) := by
  unfold right left
  rw [← sub_div]
  congr 1
  ring

theorem label_mem (n : ℕ) (hn : 0 < n) (x : ℝ) :
    ((label n hn x).val : ℝ) / n ≤ Int.fract x ∧
      Int.fract x < (((label n hn x).val : ℝ) + 1) / n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnonneg := mul_nonneg (Nat.cast_nonneg n) (Int.fract_nonneg x)
  constructor
  · apply (div_le_iff₀ hp).2
    simpa only [label_val, mul_comm] using Nat.floor_le hnonneg
  · apply (lt_div_iff₀ hp).2
    simpa only [label_val, mul_comm] using Nat.lt_floor_add_one ((n : ℝ) * Int.fract x)

theorem label_mem_iff (n : ℕ) (hn : 0 < n) (x : ℝ) (i : Fin n) :
    label n hn x = i ↔ Contains n i (Int.fract x) := by
  constructor
  · rintro rfl
    exact label_mem n hn x
  · intro hi
    have hp : (0 : ℝ) < n := by exact_mod_cast hn
    apply Fin.ext
    change ⌊(n : ℝ) * Int.fract x⌋₊ = i.val
    apply (Nat.floor_eq_iff (mul_nonneg hp.le (Int.fract_nonneg x))).2
    constructor
    · simpa only [mul_comm] using (div_le_iff₀ hp).1 hi.1
    · simpa only [mul_comm] using (lt_div_iff₀ hp).1 hi.2

/-- The literal half-open intervals cover `[0,1)` exactly once. -/
theorem existsUnique_contains (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx : 0 ≤ x ∧ x < 1) : ∃! i : Fin n, Contains n i x := by
  have hf : Int.fract x = x := Int.fract_eq_self.2 hx
  refine ⟨label n hn x, ?_, ?_⟩
  · simpa only [hf] using (label_mem_iff n hn x (label n hn x)).1 rfl
  · intro i hi
    exact ((label_mem_iff n hn x i).2 (by simpa only [hf] using hi)).symm

@[simp] theorem label_add_int (n : ℕ) (hn : 0 < n) (x : ℝ) (z : ℤ) :
    label n hn (x + z) = label n hn x := by
  apply Fin.ext
  simp only [label_val, Int.fract_add_intCast]

theorem label_eq_of_integer_difference (n : ℕ) (hn : 0 < n) (x y : ℝ)
    (h : ∃ z : ℤ, x - y = z) : label n hn x = label n hn y := by
  apply Fin.ext
  simp only [label_val, Int.fract_eq_fract.2 h]

/-- Integer floor modulo n recovers the literal fractional-part label. -/
theorem label_cast_eq_emod (n : ℕ) (hn : 0 < n) (x : ℝ) :
    ((label n hn x).val : ℤ) = ⌊(n : ℝ) * x⌋ % (n : ℤ) := by
  have hnonneg := mul_nonneg (Nat.cast_nonneg n) (Int.fract_nonneg x)
  have hf : ((label n hn x).val : ℤ) =
      ⌊(n : ℝ) * x⌋ - (n : ℤ) * ⌊x⌋ := by
    rw [label_val, Int.natCast_floor_eq_floor hnonneg]
    have hrewrite : (n : ℝ) * Int.fract x =
        (n : ℝ) * x - (((n : ℤ) * ⌊x⌋ : ℤ) : ℝ) := by
      simp only [Int.fract, Int.cast_mul, Int.cast_natCast]
      ring
    rw [hrewrite, Int.floor_sub_intCast]
  have hdecomp : ⌊(n : ℝ) * x⌋ =
      ((label n hn x).val : ℤ) + (n : ℤ) * ⌊x⌋ := by omega
  rw [hdecomp, Int.add_mul_emod_self_left, Int.emod_eq_of_lt]
  · exact Int.natCast_nonneg _
  · exact_mod_cast (label n hn x).isLt

theorem label_eq_of_floor_eq (n : ℕ) (hn : 0 < n) (x y : ℝ)
    (h : ⌊(n : ℝ) * x⌋ = ⌊(n : ℝ) * y⌋) : label n hn x = label n hn y := by
  apply Fin.ext
  have hc : ((label n hn x).val : ℤ) = ((label n hn y).val : ℤ) := by
    rw [label_cast_eq_emod, label_cast_eq_emod, h]
  exact_mod_cast hc

/-- Precisely the lifted lattice endpoints lying in a closed target interval. -/
def liftedEndpoints (n : ℕ) (a b : ℝ) : Finset ℤ :=
  Finset.Icc ⌈(n : ℝ) * a⌉ ⌊(n : ℝ) * b⌋

theorem mem_liftedEndpoints (n : ℕ) (hn : 0 < n) (a b : ℝ) (j : ℤ) :
    j ∈ liftedEndpoints n a b ↔ a ≤ (j : ℝ) / n ∧ (j : ℝ) / n ≤ b := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [liftedEndpoints, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨(le_div_iff₀ hp).2 (by simpa only [mul_comm] using hl),
      (div_le_iff₀ hp).2 (by simpa only [mul_comm] using hu)⟩
  · rintro ⟨hl, hu⟩
    exact ⟨by simpa only [mul_comm] using (le_div_iff₀ hp).1 hl,
      by simpa only [mul_comm] using (div_le_iff₀ hp).1 hu⟩

/-- The closed interval may meet both extreme endpoints; hence four, not three. -/
theorem card_liftedEndpoints_le_four (n : ℕ) (hn : 0 < n) (a b : ℝ)
    (hwidth : b - a ≤ 3 / (n : ℝ)) : (liftedEndpoints n a b).card ≤ 4 := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : (n : ℝ) * (b - a) ≤ 3 := by
    simpa only [mul_comm] using (le_div_iff₀ hp).1 hwidth
  have hr : ((⌊(n : ℝ) * b⌋ + 1 - ⌈(n : ℝ) * a⌉ : ℤ) : ℝ) ≤ 4 := by
    push_cast
    nlinarith [Int.floor_le ((n : ℝ) * b), Int.le_ceil ((n : ℝ) * a)]
  have hi : ⌊(n : ℝ) * b⌋ + 1 - ⌈(n : ℝ) * a⌉ ≤ (4 : ℤ) := by exact_mod_cast hr
  rw [liftedEndpoints, Int.card_Icc]
  omega

private theorem floor_le_of_signs_eq (n : ℕ) (hn : 0 < n) (a b x y : ℝ)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hsign : ∀ j ∈ liftedEndpoints n a b,
      ternarySign (x - (j : ℝ) / n) = ternarySign (y - (j : ℝ) / n)) :
    ⌊(n : ℝ) * x⌋ ≤ ⌊(n : ℝ) * y⌋ := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  by_contra h
  let j : ℤ := ⌊(n : ℝ) * y⌋ + 1
  have hjfloor : j ≤ ⌊(n : ℝ) * x⌋ := by dsimp [j]; omega
  have hyj : y < (j : ℝ) / n := by
    apply (lt_div_iff₀ hp).2
    simpa only [j, Int.cast_add, Int.cast_one, mul_comm] using
      Int.lt_floor_add_one ((n : ℝ) * y)
  have hjx : (j : ℝ) / n ≤ x := by
    apply (div_le_iff₀ hp).2
    simpa only [mul_comm] using (Int.le_floor.1 hjfloor)
  have hj : j ∈ liftedEndpoints n a b :=
    (mem_liftedEndpoints n hn a b j).2 ⟨hy.1.trans hyj.le, hjx.trans hx.2⟩
  have hyzero : ternarySign (y - (j : ℝ) / n) = 0 :=
    (ternarySign_eq_zero _).2 (sub_neg.mpr hyj)
  have hxneg : x - (j : ℝ) / n < 0 :=
    (ternarySign_eq_zero _).1 ((hsign j hj).trans hyzero)
  linarith

/-- Literal-label factorization through finitely many ternary comparisons.
No width or counting premise is needed for this determination statement. -/
theorem label_eq_of_signs_eq (n : ℕ) (hn : 0 < n) (a b x y : ℝ)
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hsign : ∀ j ∈ liftedEndpoints n a b,
      ternarySign (x - (j : ℝ) / n) = ternarySign (y - (j : ℝ) / n)) :
    label n hn x = label n hn y := by
  apply label_eq_of_floor_eq n hn x y
  exact le_antisymm (floor_le_of_signs_eq n hn a b x y hx hy hsign)
    (floor_le_of_signs_eq n hn a b y x hy hx (fun j hj => (hsign j hj).symm))

end

end QuantitativeVanDerWaerden.UniformMesh

end OAI
