import OAI.NumberTheory.Ostmann.Construction.InitialMovingWeight

namespace OAI

/-! # The original half-list weights through the complete moving tree -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def initialMovingRealWeight {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) : ℝ :=
  (initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (i.castAdd b))) *
    initialLogSumWeight value cd sl) *
  (initialLogSumWeight value cb (fun i : Fin b => y ((), .inr (Fin.natAdd b i))) *
    initialLogSumWeight value cd sr)

theorem initialMovingRealWeight_cast {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    (initialMovingRealWeight value b d r cb cd sl sr y : ℂ) =
      initialMovingCutoffWeight value b d r cb cd sl sr y := by
  exact Complex.ofReal_mul _ _

theorem initialMovingRealWeight_bounds {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P)
    (y : MovingRegularSlot 0 (r + r) (b + b) → P) :
    0 ≤ initialMovingRealWeight value b d r cb cd sl sr y ∧
      initialMovingRealWeight value b d r cb cd sl sr y ≤ 1 := by
  have h0 : 0 ≤ initialMovingRealWeight value b d r cb cd sl sr y := by
    unfold initialMovingRealWeight
    exact mul_nonneg (mul_nonneg (initialLogSumWeight_nonneg _ _ _) (initialLogSumWeight_nonneg _ _ _))
      (mul_nonneg (initialLogSumWeight_nonneg _ _ _) (initialLogSumWeight_nonneg _ _ _))
  refine ⟨h0, ?_⟩
  have h := initialMovingCutoffWeight_norm_le_one value b d r cb cd sl sr y
  rw [← initialMovingRealWeight_cast, Complex.norm_real, Real.norm_of_nonneg h0] at h
  exact h

noncomputable def initialMovingTreeWeight {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P) :
    {n : ℕ} → MovingSlotData P n → ℝ
  | _, T@(.leaf _ _) => initialMovingRealWeight value b d r cb cd sl sr
      (initialRegularFromList b r fallback T.regularSlots)
  | _, .node _ _ _ _ left right =>
      initialMovingTreeWeight value b d r cb cd sl sr fallback left *
        initialMovingTreeWeight value b d r cb cd sl sr fallback right

theorem initialMovingTreeWeight_bounds {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    {n : ℕ} (T : MovingSlotData P n) :
    0 ≤ initialMovingTreeWeight value b d r cb cd sl sr fallback T ∧
      initialMovingTreeWeight value b d r cb cd sl sr fallback T ≤ 1 := by
  induction T with
  | leaf => exact initialMovingRealWeight_bounds value b d r cb cd sl sr _
  | node s CL CR U l rr ihL ihR =>
    exact ⟨mul_nonneg ihL.1 ihR.1,
      (mul_le_mul ihL.2 ihR.2 ihR.1 zero_le_one).trans_eq (one_mul 1)⟩

theorem initialMovingDataCutoff_factor {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    {n : ℕ} (T : MovingSlotData P n) (s : ℤ) :
    initialMovingDataCutoff value b d r cb cd sl sr fallback T s =
      (initialMovingRealWeight value b d r cb cd sl sr
        (initialRegularFromList b r fallback T.regularSlots) : ℂ) *
        (if s = 0 then 0 else 1) := by
  rw [initialMovingRealWeight_cast]
  unfold initialMovingDataCutoff
  split_ifs <;> simp only [mul_zero, mul_one]

theorem movingDataWeight_initial_factor {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (F : {n : ℕ} → MovingSlotData P n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData P n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData P n) :
    movingDataWeight (fun T s => initialMovingDataCutoff value b d r cb cd sl sr fallback T s * F T s) E T =
      (initialMovingTreeWeight value b d r cb cd sl sr fallback T : ℂ) *
        movingDataWeight (fun T s => (if s = 0 then 0 else 1) * F T s) E T := by
  induction T with
  | leaf s regular =>
    simp only [movingDataWeight, initialMovingTreeWeight, initialMovingDataCutoff_factor, mul_assoc]
  | node s CL CR U l rr ihL ihR =>
    simp only [movingDataWeight, initialMovingTreeWeight, ihL, ihR, Complex.ofReal_mul,
      star_mul, Complex.star_def, Complex.conj_ofReal]
    ring

theorem movingDataWeight_initial_norm_le {P : Type*} (value : P → ℕ)
    (b d r : ℕ) (cb cd : ℝ) (sl sr : Fin d → P) (fallback : P)
    (F : {n : ℕ} → MovingSlotData P n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData P n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData P n) :
    ‖movingDataWeight (fun T s => initialMovingDataCutoff value b d r cb cd sl sr fallback T s * F T s) E T‖ ≤
      ‖movingDataWeight (fun T s => (if s = 0 then 0 else 1) * F T s) E T‖ := by
  rw [movingDataWeight_initial_factor, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (initialMovingTreeWeight_bounds value b d r cb cd sl sr fallback T).1]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (initialMovingTreeWeight_bounds value b d r cb cd sl sr fallback T).2

end Ostmann

end OAI
