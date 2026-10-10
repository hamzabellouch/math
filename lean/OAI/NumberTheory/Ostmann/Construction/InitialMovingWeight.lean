import OAI.NumberTheory.Ostmann.Construction.InitialMovingData
import OAI.NumberTheory.Ostmann.Arithmetic.MovingLeafAmplitude

namespace OAI

/-! # Bounds retained by the two original half-list cutoffs -/
namespace Ostmann
open scoped Classical BigOperators

private theorem initialLogSumWeight_live {P : Type*} {n : ℕ} (value : P → ℕ)
    (c : ℝ) (x : Fin n → P) (hx : initialLogSumWeight value c x ≠ 0) :
    |(∑ i, Real.log (value (x i) : ℝ)) - c| < 1 := by
  by_contra hn
  exact hx (logCellProfile_zero_outside _ (le_of_not_gt hn))

theorem initialMovingCutoffWeight_norm_le_one {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    ‖initialMovingCutoffWeight value b d r cb cd sl sr y‖ ≤ 1 := by
  have h (x : Fin b → P) (s : Fin d → P) :
      ‖((initialLogSumWeight value cb x * initialLogSumWeight value cd s : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg
      (initialLogSumWeight_nonneg _ _ _) (initialLogSumWeight_nonneg _ _ _))]
    exact (mul_le_mul (initialLogSumWeight_le_one _ _ _) (initialLogSumWeight_le_one _ _ _)
      (initialLogSumWeight_nonneg _ _ _) zero_le_one).trans_eq (one_mul 1)
  unfold initialMovingCutoffWeight
  rw [norm_mul]
  exact (mul_le_mul (h _ _) (h _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem initialMovingCutoffWeight_live_sums {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (hy : initialMovingCutoffWeight value b d r cb cd sl sr y ≠ 0) :
    |(∑ i : Fin (b + b), Real.log (value (y ((), .inr i)) : ℝ)) - 2 * cb| < 2 ∧
      |(∑ i : Fin (d + d), Real.log (value (Fin.append sl sr i) : ℝ)) - 2 * cd| < 2 := by
  have hl := left_ne_zero_of_mul hy
  have hr := right_ne_zero_of_mul hy
  have hl' : initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (i.castAdd b))) *
      initialLogSumWeight value cd sl ≠ 0 := by exact_mod_cast hl
  have hr' : initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (Fin.natAdd b i))) *
      initialLogSumWeight value cd sr ≠ 0 := by exact_mod_cast hr
  have hbl := initialLogSumWeight_live value cb _ (left_ne_zero_of_mul hl')
  have hbr := initialLogSumWeight_live value cb _ (left_ne_zero_of_mul hr')
  have hdl := initialLogSumWeight_live value cd sl (right_ne_zero_of_mul hl')
  have hdr := initialLogSumWeight_live value cd sr (right_ne_zero_of_mul hr')
  constructor
  · rw [Fin.sum_univ_add]
    obtain ⟨hbl, hbl'⟩ := abs_lt.mp hbl
    obtain ⟨hbr, hbr'⟩ := abs_lt.mp hbr
    apply abs_lt.mpr
    constructor <;> linarith only [hbl, hbl', hbr, hbr']
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    obtain ⟨hdl, hdl'⟩ := abs_lt.mp hdl
    obtain ⟨hdr, hdr'⟩ := abs_lt.mp hdr
    apply abs_lt.mpr
    constructor <;> linarith only [hdl, hdl', hdr, hdr']

theorem initialMovingCutoffWeight_bulk_product_lower {P : Type*} (value : P → ℕ)
    (hvalue : ∀ p, 0 < value p) (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P)
    (hy : initialMovingCutoffWeight value b d r cb cd sl sr y ≠ 0) :
    Real.exp (2 * cb - 2) < (∏ i : Fin (b + b), (value (y ((), .inr i)) : ℝ)) := by
  have h := (abs_lt.mp (initialMovingCutoffWeight_live_sums value b d r cb cd sl sr y hy).1).1
  have hp : 0 < ∏ i : Fin (b + b), (value (y ((), .inr i)) : ℝ) :=
    Finset.prod_pos (fun i _ => by exact_mod_cast hvalue (y ((), .inr i)))
  apply (Real.lt_log_iff_exp_lt hp).mp
  rw [Real.log_prod (fun i _ => by exact_mod_cast (hvalue (y ((), .inr i))).ne')]
  linarith

theorem initialMovingDataCutoff_norm_le_one {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    {n : ℕ} (T : MovingSlotData P n) (s : ℤ) :
    ‖initialMovingDataCutoff value b d r cb cd sl sr fallback T s‖ ≤ 1 := by
  unfold initialMovingDataCutoff
  split_ifs
  · simp only [norm_zero, zero_le_one]
  · exact initialMovingCutoffWeight_norm_le_one value b d r cb cd sl sr _

theorem initialMovingDataWeight_norm_le_one {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    {n : ℕ} (T : MovingSlotData P n) :
    ‖movingDataWeight (initialMovingDataCutoff value b d r cb cd sl sr fallback)
      (fun _ _ _ _ => 1) T‖ ≤ 1 :=
  movingDataWeight_unit_norm_le_one _ (fun _ _ => initialMovingDataCutoff_norm_le_one
    value b d r cb cd sl sr fallback _ _) T

end Ostmann

end OAI
