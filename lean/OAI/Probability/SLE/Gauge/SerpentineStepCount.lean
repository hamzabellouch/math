import OAI.Probability.SLE.Gauge.RibbonConcatenation

namespace OAI

/-! Integer unit-step alignment inside the actual straight passes of the
serpentine array. A full unit middle strip is retained in each selected
step; rounding the column entry times does not lose the quadratic count. -/

noncomputable section
open Set
open scoped NNReal

namespace SLEExactGauge.Serpentine

/-- Column entry times in ribbon-width units: straight length `200m`,
then a semicircle of radius 50. The connector contributes `A`. -/
def columnEntry (A : ℝ) (m j : ℕ) : ℝ :=
  A + j * (200 * (m : ℝ) + 50 * Real.pi)

def retainedStep (A : ℝ) (m j i : ℕ) : ℕ := ⌈columnEntry A m j⌉₊ + i + 1

lemma columnEntry_nonneg {A : ℝ} (hA : 0 ≤ A) (m j : ℕ) :
    0 ≤ columnEntry A m j := by
  unfold columnEntry
  positivity

lemma retainedStep_bounds {A : ℝ} (hA : 0 ≤ A) {m j i : ℕ}
    (hi : i < m) :
    columnEntry A m j + 1 ≤ retainedStep A m j i ∧
      (retainedStep A m j i : ℝ) < columnEntry A m j + m + 1 := by
  have hl := Nat.le_ceil (columnEntry A m j)
  have hu := Nat.ceil_lt_add_one (columnEntry_nonneg hA m j)
  have hir : (i : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt hi
  simp only [retainedStep, Nat.cast_add, Nat.cast_one]
  constructor
  · have hiz : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  · linarith

/-- The complete closed middle interval of each chosen integer step lies
strictly in its corresponding straight pass. -/
theorem retained_middle_in_straight {A : ℝ} (hA : 0 ≤ A) {m j i : ℕ}
    (hi : i < m) :
    Icc ((retainedStep A m j i : ℝ) + 1 / 3)
      ((retainedStep A m j i : ℝ) + 2 / 3) ⊆
      Ioo (columnEntry A m j) (columnEntry A m j + 200 * m) := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast Nat.succ_le_of_lt (Nat.zero_le i |>.trans_lt hi)
  obtain ⟨hl, hu⟩ := retainedStep_bounds hA hi
  intro t ht
  constructor <;> linarith [ht.1, ht.2]

lemma columnEntry_separation {A : ℝ} {m j k : ℕ} (hm : 0 < m) (hjk : j < k) :
    columnEntry A m j + 200 * m ≤ columnEntry A m k := by
  have hjkr : (j : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt hjk
  have hperiod : 0 ≤ 200 * (m : ℝ) + 50 * Real.pi := by positivity
  have hh := mul_le_mul_of_nonneg_right hjkr hperiod
  unfold columnEntry
  nlinarith [Real.pi_pos]

lemma retainedStep_strict_column {A : ℝ} (hA : 0 ≤ A) {m j k i l : ℕ}
    (hm : 0 < m) (hjk : j < k) (hi : i < m) (hl : l < m) :
    retainedStep A m j i < retainedStep A m k l := by
  obtain ⟨_, hui⟩ := retainedStep_bounds hA hi
  obtain ⟨hll, _⟩ := retainedStep_bounds hA hl
  have hsep := columnEntry_separation (A := A) hm hjk
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hh : (retainedStep A m j i : ℝ) < retainedStep A m k l := by linarith
  exact_mod_cast hh

theorem retainedStep_injective {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 0 < m) :
    Function.Injective (fun ji : Fin m × Fin m => retainedStep A m ji.1 ji.2) := by
  rintro ⟨j, i⟩ ⟨k, l⟩ he
  have hjk : j = k := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hh := retainedStep_strict_column hA hm hlt i.isLt l.isLt
      exact (ne_of_lt hh) he
    · have hh := retainedStep_strict_column hA hm hgt l.isLt i.isLt
      exact (ne_of_lt hh) he.symm
  subst k
  have hil : i = l := by
    apply Fin.ext
    change ⌈columnEntry A m (j : ℕ)⌉₊ + (i : ℕ) + 1 =
      ⌈columnEntry A m (j : ℕ)⌉₊ + (l : ℕ) + 1 at he
    omega
  subst l
  rfl

def retainedSteps (A : ℝ) (m : ℕ) : Finset ℕ :=
  Finset.univ.image (fun ji : Fin m × Fin m => retainedStep A m ji.1 ji.2)

theorem retainedSteps_card {A : ℝ} (hA : 0 ≤ A) {m : ℕ} (hm : 0 < m) :
    (retainedSteps A m).card = m ^ 2 := by
  rw [retainedSteps, Finset.card_image_of_injective _ (retainedStep_injective hA hm)]
  simp [pow_two]

/-- Rounded completion of all `2m+1` passes, before extending vertically. -/
def completionStep (A : ℝ) (m : ℕ) : ℕ :=
  ⌈columnEntry A m (2 * m) + 200 * (m : ℝ)⌉₊

theorem completionStep_quadratic_bound {A A₀ : ℝ} (hA : 0 ≤ A) (hA₀ : 0 ≤ A₀)
    {m : ℕ} (hm : 0 < m) (hbound : A ≤ A₀ * m) :
    (completionStep A m : ℝ) ≤ (A₀ + 601 + 100 * Real.pi) * (m : ℝ) ^ 2 := by
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hAn := mul_le_mul_of_nonneg_left hsq hA₀
  have hπn := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 100 * Real.pi by positivity)
  have hl := Nat.ceil_lt_add_one
    (show 0 ≤ columnEntry A m (2 * m) + 200 * (m : ℝ) by
      exact add_nonneg (columnEntry_nonneg hA m (2 * m)) (by positivity))
  change (completionStep A m : ℝ) < _ at hl
  unfold completionStep columnEntry at *
  push_cast at hl ⊢
  nlinarith


end SLEExactGauge.Serpentine

end

end OAI
