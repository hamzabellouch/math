import OAI.NumberTheory.Ostmann.Arithmetic.MovingSupportWeight
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFourierSupported

namespace OAI

/-! # The remaining original scalar and its literal terminal windows -/

namespace Ostmann
open scoped Classical

noncomputable def movingDataLeaf {σ : Type*}
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ) (x : MovingSlotState σ) (s : ℤ) : ℂ :=
  F x.data s

noncomputable def movingDataExtra {σ : Type*}
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (x : MovingSlotState σ) (s v w : ℤ) : ℝ := E x.data s v w

noncomputable def movingDataWeight {σ : Type*}
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ) :
    {n : ℕ} → MovingSlotData σ n → ℂ
  | _, T@(.leaf s _) => F T s
  | _, T@(.node s _ _ _ left right) =>
      (E T s left.frequency right.frequency : ℂ) * movingDataWeight F E left *
        star (movingDataWeight F E right)

theorem movingUnrestrictedWeight_data {σ : Type*} (value : σ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    movingUnrestrictedWeight value (movingDataLeaf F) (movingDataExtra E) T XL XR =
      movingDataWeight F E T := by
  induction T generalizing XL XR with
  | leaf => rfl
  | node s CL CR U left right ihL ihR =>
    simp only [movingUnrestrictedWeight, movingDataExtra, ihL, ihR, movingDataWeight]

/-- Sharp terminal windows leave one fixed scalar coefficient. The test is
on the actual terminal moduli obtained by the integer moving recursion. -/
theorem movingUnrestrictedWeight_data_window {σ : Type*} (value : σ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (X lo hi : ℝ) {n : ℕ} (T : MovingSlotData σ n) (XL XR : ℕ) :
    movingUnrestrictedWeight value (movingWindowLeaf value X lo hi (movingDataLeaf F))
        (movingDataExtra E) T XL XR =
      if ∀ i, (T.leafModuli value XL XR i : ℝ) / X ∈ Set.Icc lo hi
      then movingDataWeight F E T else 0 := by
  induction T generalizing XL XR with
  | leaf s regular =>
    simp only [movingUnrestrictedWeight, movingWindowLeaf, movingSlotModulus,
      movingDataLeaf, movingDataWeight, MovingSlotData.leafModuli, forall_const]
    rfl
  | @node n s CL CR U left right ihL ihR =>
    let p := (MovingSlotData.step s CL CR U left right false).naturalPivot value XL XR
    have hforall : (∀ i, ((MovingSlotData.node s CL CR U left right).leafModuli value XL XR i : ℝ) / X ∈ Set.Icc lo hi) ↔
        (∀ i, (left.leafModuli value p XL i : ℝ) / X ∈ Set.Icc lo hi) ∧
        (∀ i, (right.leafModuli value p XR i : ℝ) / X ∈ Set.Icc lo hi) := by
      constructor
      · intro h
        exact ⟨fun i => h (.inl i), fun i => h (.inr i)⟩
      · rintro ⟨hL, hR⟩ i
        cases i with
        | inl i => exact hL i
        | inr i => exact hR i
    rw [movingUnrestrictedWeight, ihL, ihR]
    simp only [movingDataExtra, movingDataWeight, hforall]
    by_cases hL : ∀ i, (left.leafModuli value p XL i : ℝ) / X ∈ Set.Icc lo hi <;>
      by_cases hR : ∀ i, (right.leafModuli value p XR i : ℝ) / X ∈ Set.Icc lo hi <;>
      simp only [p, hL, hR, forall_const, and_self, and_false, false_and, ite_true, ite_false,
        star_zero, zero_mul, mul_zero]

end Ostmann

end OAI
