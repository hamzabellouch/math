import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportWeight

namespace OAI

/-! # The actual recursive coefficient on real moving giants -/

namespace Ostmann
open scoped Classical

/-- Real evaluation of the very same moving recursion, before arithmetic
indicators. The reciprocal compensation product remains in every pivot. -/
noncomputable def movingRealWeight {σ : Type*} (value : σ → ℕ)
    (F : ∀ {n}, MovingSlotData σ n → ℝ → ℝ → ℂ)
    (E : ∀ {n}, MovingSlotData σ n → ℝ → ℝ → ℝ) :
    {n : ℕ} → MovingSlotData σ n → ℝ → ℝ → ℂ
  | _, .leaf s regular, L, R => F (.leaf s regular) L R
  | _, .node s CL CR u left right, L, R =>
      let p := (MovingSlotData.step s CL CR u left right false).realPivot value L R
      (E (.node s CL CR u left right) L R : ℂ) *
        movingRealWeight value F E left p L * star (movingRealWeight value F E right p R)

noncomputable def movingRealLeaf {σ : Type*}
    (F : ∀ {n}, MovingSlotData σ n → ℝ → ℝ → ℂ) (x : MovingSlotState σ) (_s : ℤ) : ℂ :=
  F x.data x.leftGiant x.rightGiant

noncomputable def movingRealExtra {σ : Type*}
    (E : ∀ {n}, MovingSlotData σ n → ℝ → ℝ → ℝ)
    (x : MovingSlotState σ) (_s _v _w : ℤ) : ℝ :=
  E x.data x.leftGiant x.rightGiant

/-- Agreement uses the proved integer recursion, not a new realization
hypothesis for each of the polynomial leaves. -/
theorem movingRealWeight_eq_unrestricted {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0)
    (F : ∀ {n}, MovingSlotData σ n → ℝ → ℝ → ℂ)
    (E : ∀ {n}, MovingSlotData σ n → ℝ → ℝ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (hf : T.Frequencies (· ≠ 0))
    (XL XR : ℕ) (hI : T.Integral value XL XR) :
    movingRealWeight value F E T XL XR =
      movingUnrestrictedWeight value (movingRealLeaf F) (movingRealExtra E) T XL XR := by
  induction T generalizing XL XR with
  | leaf => rfl
  | node s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right false
    have hp := step.realPivot_eq value XL XR hf.1
      (MovingSlotReversal.naturalProduct_ne_zero value hvalue u) hI.1
    dsimp only [step] at hp
    simp only [movingRealWeight, hp, movingUnrestrictedWeight, movingRealExtra]
    rw [ihL hf.2.1 _ _ hI.2.1, ihR hf.2.2 _ _ hI.2.2]

/-- Exact smooth/arithmetic separation for the original recursive weight.
All invalid integer reconstructions are retained as zero terms. -/
theorem movingSlotWeight_real_factor {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : ∀ {n}, MovingSlotData σ n → ℝ → ℝ → ℂ)
    (E : ∀ {n}, MovingSlotData σ n → ℝ → ℝ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR : ℕ) :
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound) (movingRealLeaf F)
      (movingSlotCutoff value childBound pivotBound (movingRealExtra E)) n ⟨n, T, XL, XR⟩ t =
        movingArithmeticIndicator value childBound pivotBound T XL XR *
          movingRealWeight value F E T XL XR := by
  rw [movingSlotWeight_indicator_factor value hvalue childBound pivotBound _ _ T t hT hf]
  by_cases hs : T.ArithmeticSupport value childBound pivotBound XL XR
  · rw [movingRealWeight_eq_unrestricted value hvalue F E T hf XL XR
      (hs.integral value hvalue childBound pivotBound T XL XR)]
  · simp only [movingArithmeticIndicator, ite_eq_right hs, zero_mul]

/-- Once the indicator is fixed on a residue/root cell, its contribution to
an oscillation is at most that of the explicit real weight. -/
theorem movingSlotWeight_real_cell_difference {σ : Type*} (value : σ → ℕ)
    (hvalue : ∀ i, value i ≠ 0) (childBound pivotBound : ℕ → ℕ)
    (F : ∀ {n}, MovingSlotData σ n → ℝ → ℝ → ℂ)
    (E : ∀ {n}, MovingSlotData σ n → ℝ → ℝ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL YL XR : ℕ)
    (hres : (XL : ℤ) ≡ (YL : ℤ) [ZMOD movingTopPeriod value hvalue childBound pivotBound T hf])
    (hcell : rootCellCode (movingTopRootCuts value hvalue childBound pivotBound T hf XR) (XL : ℝ) =
      rootCellCode (movingTopRootCuts value hvalue childBound pivotBound T hf XR) (YL : ℝ)) :
    ‖recursiveTransferWeight (movingSlotSystem value childBound pivotBound) (movingRealLeaf F)
        (movingSlotCutoff value childBound pivotBound (movingRealExtra E)) n ⟨n, T, XL, XR⟩ t -
      recursiveTransferWeight (movingSlotSystem value childBound pivotBound) (movingRealLeaf F)
        (movingSlotCutoff value childBound pivotBound (movingRealExtra E)) n ⟨n, T, YL, XR⟩ t‖ ≤
      ‖movingRealWeight value F E T XL XR - movingRealWeight value F E T YL XR‖ := by
  rw [movingSlotWeight_real_factor value hvalue childBound pivotBound F E T t hT hf,
    movingSlotWeight_real_factor value hvalue childBound pivotBound F E T t hT hf,
    movingArithmeticIndicator_cells value hvalue childBound pivotBound T hf XL YL XR hres hcell,
    ← mul_sub, norm_mul]
  by_cases hs : T.ArithmeticSupport value childBound pivotBound YL XR
  · simp only [movingArithmeticIndicator, ite_eq_left hs, norm_one, one_mul, le_refl]
  · simp only [movingArithmeticIndicator, ite_eq_right hs, norm_zero, zero_mul, norm_nonneg]

end Ostmann

end OAI
