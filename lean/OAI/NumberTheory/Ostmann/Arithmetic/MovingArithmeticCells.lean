import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportWeight
import OAI.NumberTheory.Ostmann.Arithmetic.RootCellPrimeComparison

namespace OAI

/-! # Exact root-cell multipliers for the original moving arithmetic support -/

namespace Ostmann
open scoped Classical

theorem rootCellCode_eq_of_subset (S T : Finset ℝ) (hST : S ⊆ T) (x y : ℝ)
    (h : rootCellCode T x = rootCellCode T y) : rootCellCode S x = rootCellCode S y := by
  funext r
  exact congrFun h ⟨r.val, hST r.property⟩

/-- A cell is accepted precisely when it contains an original supported
integer in the prescribed progression. Invariance supplies the converse. -/
noncomputable def movingArithmeticCellValue {σ : Type*} (value : σ → ℕ)
    (_hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (_hf : T.Frequencies (· ≠ 0)) (XR a M : ℕ)
    (S : Finset ℝ) (code : S → Ordering) : ℂ :=
  if ∃ XL : ℕ,
      (XL : ℤ) ≡ (a : ℤ) [ZMOD M] ∧
      rootCellCode S (XL : ℝ) = code ∧ T.ArithmeticSupport value childBound pivotBound XL XR
    then 1 else 0

theorem movingArithmeticCellValue_norm {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a M : ℕ)
    (S : Finset ℝ) (code : S → Ordering) :
    ‖movingArithmeticCellValue value hvalue childBound pivotBound T hf XR a M S code‖ ≤ 1 := by
  unfold movingArithmeticCellValue
  split_ifs <;> norm_num

/-- Adding derivative roots to the arithmetic cuts does not change the
exact support multiplier on any integer in the progression. -/
theorem movingArithmeticIndicator_eq_cell {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XL XR a M : ℕ)
    (S : Finset ℝ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hS : movingTopRootCuts value hvalue childBound pivotBound T hf XR ⊆ S)
    (hres : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) :
    movingArithmeticIndicator value childBound pivotBound T XL XR =
      movingArithmeticCellValue value hvalue childBound pivotBound T hf XR a M S
        (rootCellCode S (XL : ℝ)) := by
  unfold movingArithmeticIndicator movingArithmeticCellValue
  congr 1
  apply propext
  constructor
  · intro hx
    exact ⟨XL, hres, rfl, hx⟩
  · rintro ⟨YL, hyres, hycode, hysupp⟩
    exact (moving_top_support_cells value hvalue childBound pivotBound T hf YL XL XR
      ((hyres.trans hres.symm).of_dvd (by exact_mod_cast hM)) (rootCellCode_eq_of_subset _ S hS _ _ hycode)).mp hysupp

theorem complexPrimeInterval_congr (q a : ℕ) (u v : ℝ) (w g : ℝ → ℂ)
    (h : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      p.Prime → Nat.ModEq q p a → w (Real.log p) = g (Real.log p)) :
    complexPrimeInterval q a u v w = complexPrimeInterval q a u v g := by
  unfold complexPrimeInterval
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hc : p.Prime ∧ Nat.ModEq q p a
  · simp only [ite_eq_left hc, h p hp hc.1 hc.2]
  · simp only [ite_eq_right hc]

/-- The exact original arithmetic indicator becomes the constructed root-cell
multiplier under the actual prime sum, with every boundary prime included. -/
theorem movingArithmeticPrimeInterval_cells {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0)) (XR a M : ℕ)
    (S : Finset ℝ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hS : movingTopRootCuts value hvalue childBound pivotBound T hf XR ⊆ S)
    (u v : ℝ) (w : ℝ → ℂ) :
    complexPrimeInterval M a u v
      (fun y => movingArithmeticIndicator value childBound pivotBound T ⌊Real.exp y⌋₊ XR * w y) =
    complexPrimeInterval M a u v
      (fun y => movingArithmeticCellValue value hvalue childBound pivotBound T hf XR a M S
        (rootCellCode S (Real.exp y)) * w y) := by
  apply complexPrimeInterval_congr
  intro p hp hprime hpa
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  rw [Real.exp_log hp0, Nat.floor_natCast]
  rw [movingArithmeticIndicator_eq_cell value hvalue childBound pivotBound T hf p XR a M S hM hS
    (Int.natCast_modEq_iff.mpr hpa)]

end Ostmann

end OAI
