import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

universe uI

/-!
# Finite codes for downward rounding of grouped weights

For a positive mesh `δ`, a weight in `[0, 1]` is rounded down to
`δ * floor (w / δ)`. Its integer coefficient is an actual element of
`Fin (floor (1 / δ) + 1)`, including the possible endpoint `w = 1`.
The error estimates apply to every indicator with values in `[0, 1]`.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

/-- The number of possible rounded values of a weight in `[0, 1]`. -/
def weightCodeSize (δ : ℝ) : ℕ := Nat.floor (1 / δ) + 1

theorem weightCodeSize_pos (δ : ℝ) : 0 < weightCodeSize δ :=
  Nat.succ_pos _

/-- Downward rounding to the mesh `δ`. -/
def roundWeight (δ w : ℝ) : ℝ := δ * (Nat.floor (w / δ) : ℝ)

/-- Decode an integer weight code using the fixed mesh. -/
def decodeWeight (δ : ℝ) (c : Fin (weightCodeSize δ)) : ℝ := δ * (c.val : ℝ)

/-- The integer coefficient of every rounded weight is within the finite code
range. The positivity and interval hypotheses are explicit. -/
def weightCode (δ w : ℝ) (hδ : 0 < δ) (_hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    Fin (weightCodeSize δ) :=
  ⟨Nat.floor (w / δ), Nat.lt_succ_of_le
    (Nat.floor_mono ((div_le_div_iff_of_pos_right hδ).2 hw1))⟩

@[simp] theorem weightCode_val (δ w : ℝ) (hδ : 0 < δ) (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1) :
    (weightCode δ w hδ hw0 hw1).val = Nat.floor (w / δ) := rfl

@[simp] theorem decodeWeight_weightCode (δ w : ℝ) (hδ : 0 < δ) (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1) :
    decodeWeight δ (weightCode δ w hδ hw0 hw1) = roundWeight δ w := rfl

@[simp] theorem roundWeight_zero (δ : ℝ) : roundWeight δ 0 = 0 := by
  simp [roundWeight]

theorem roundWeight_nonneg {δ w : ℝ} (hδ : 0 ≤ δ) : 0 ≤ roundWeight δ w :=
  mul_nonneg hδ (Nat.cast_nonneg _)

theorem roundWeight_le {δ w : ℝ} (hδ : 0 < δ) (hw0 : 0 ≤ w) :
    roundWeight δ w ≤ w := by
  have hf := Nat.floor_le (div_nonneg hw0 hδ.le)
  have hm := (le_div_iff₀ hδ).mp hf
  simpa only [roundWeight, mul_comm] using hm

/-- The downward rounding error is strictly smaller than one mesh interval. -/
theorem roundWeight_sub_lt {δ w : ℝ} (hδ : 0 < δ) :
    w - roundWeight δ w < δ := by
  have hf := Nat.lt_floor_add_one (w / δ)
  have hm := (div_lt_iff₀ hδ).mp hf
  dsimp [roundWeight]
  nlinarith

theorem roundWeight_error {δ w : ℝ} (hδ : 0 < δ) (hw0 : 0 ≤ w) :
    0 ≤ w - roundWeight δ w ∧ w - roundWeight δ w < δ :=
  ⟨sub_nonneg.mpr (roundWeight_le hδ hw0), roundWeight_sub_lt hδ⟩

/-- The finite integer code count satisfies the real-valued bound used in the
compression estimate. -/
theorem weightCodeSize_le {δ : ℝ} (hδ : 0 < δ) :
    (weightCodeSize δ : ℝ) ≤ 1 + 1 / δ := by
  have hf := Nat.floor_le (div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hδ.le)
  simp only [weightCodeSize, Nat.cast_add, Nat.cast_one]
  linarith

/-- Multiplying by a number in `[0, 1]` cannot increase the rounding loss. -/
theorem roundWeight_mul_error {δ w b : ℝ} (hδ : 0 < δ) (hw0 : 0 ≤ w)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ w * b - roundWeight δ w * b ∧
      w * b - roundWeight δ w * b ≤ δ := by
  rw [← sub_mul]
  have herr := roundWeight_error hδ hw0
  exact ⟨mul_nonneg herr.1 hb0,
    (mul_le_of_le_one_right herr.1 hb1).trans herr.2.le⟩

/-- Simultaneous rounding of an actual finite array of weights loses at most
one mesh interval for each array entry. -/
theorem roundWeight_sum_error {I : Type uI} [Fintype I]
    (δ : ℝ) (hδ : 0 < δ) (w b : I → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hb0 : ∀ i, 0 ≤ b i) (hb1 : ∀ i, b i ≤ 1) :
    0 ≤ (∑ i, w i * b i) - ∑ i, roundWeight δ (w i) * b i ∧
      (∑ i, w i * b i) - ∑ i, roundWeight δ (w i) * b i ≤
        (Fintype.card I : ℝ) * δ := by
  constructor
  · rw [← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun i _ => (roundWeight_mul_error hδ (hw0 i) (hb0 i) (hb1 i)).1
  · calc
      (∑ i, w i * b i) - ∑ i, roundWeight δ (w i) * b i =
          ∑ i, (w i * b i - roundWeight δ (w i) * b i) :=
        (Finset.sum_sub_distrib (s := Finset.univ)
          (fun i : I => w i * b i)
          (fun i : I => roundWeight δ (w i) * b i)).symm
      _ ≤ ∑ _i : I, δ := Finset.sum_le_sum fun i _ =>
        (roundWeight_mul_error hδ (hw0 i) (hb0 i) (hb1 i)).2
      _ = (Fintype.card I : ℝ) * δ := by simp

/-- The mesh used for one level of the partition compression. -/
def roundingStep (θ : ℝ) (s u : ℕ) : ℝ := θ / ((s : ℝ) * 2 ^ u)

theorem roundingStep_pos {θ : ℝ} {s u : ℕ} (hθ : 0 < θ) (hs : 0 < s) :
    0 < roundingStep θ s u :=
  div_pos hθ (mul_pos (Nat.cast_pos.mpr hs) (pow_pos (by norm_num) _))

theorem slotTag_card (s u : ℕ) :
    (Fintype.card (Fin s × Finset (Fin u)) : ℝ) = (s : ℝ) * 2 ^ u := by
  simp

/-- The actual number of slot/subset pairs times the mesh equals the prescribed
per-level error. -/
theorem card_mul_roundingStep (θ : ℝ) {s u : ℕ} (hs : 0 < s) :
    (Fintype.card (Fin s × Finset (Fin u)) : ℝ) * roundingStep θ s u = θ := by
  rw [slotTag_card, roundingStep]
  exact mul_div_cancel₀ θ
    (ne_of_gt (mul_pos (Nat.cast_pos.mpr hs) (pow_pos (by norm_num) _)))

/-- The finite code size counts all
integers from zero through `floor (s * 2^u / θ)`, inclusive. -/
theorem weightCodeSize_roundingStep (θ : ℝ) (s u : ℕ) :
    weightCodeSize (roundingStep θ s u) =
      Nat.floor (((s : ℝ) * 2 ^ u) / θ) + 1 := by
  simp only [weightCodeSize, roundingStep, one_div_div]

/-- The total loss at a single level is at most `θ`, for the exact index type
`Fin s × Finset (Fin u)` used by the finite compression codes. -/
theorem roundWeight_level_error {θ : ℝ} {s u : ℕ} (hθ : 0 < θ) (hs : 0 < s)
    (w b : Fin s → Finset (Fin u) → ℝ)
    (hw0 : ∀ k T, 0 ≤ w k T) (hb0 : ∀ k T, 0 ≤ b k T)
    (hb1 : ∀ k T, b k T ≤ 1) :
    0 ≤ (∑ k, ∑ T, w k T * b k T) -
        ∑ k, ∑ T, roundWeight (roundingStep θ s u) (w k T) * b k T ∧
      (∑ k, ∑ T, w k T * b k T) -
        ∑ k, ∑ T, roundWeight (roundingStep θ s u) (w k T) * b k T ≤ θ := by
  have herr := roundWeight_sum_error (roundingStep θ s u) (roundingStep_pos hθ hs)
    (fun i : Fin s × Finset (Fin u) => w i.1 i.2)
    (fun i : Fin s × Finset (Fin u) => b i.1 i.2)
    (fun i => hw0 i.1 i.2) (fun i => hb0 i.1 i.2) (fun i => hb1 i.1 i.2)
  rw [card_mul_roundingStep θ hs] at herr
  simpa only [Fintype.sum_prod_type] using herr

end MetricEntropyDuality

end

end OAI
