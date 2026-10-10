import Mathlib
import OAI.LinearAlgebra.MatrixFields.Histories.InheritedMaskMargins

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.Subdivision

open MatrixMultiplication.Foundation InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Type*) [∀ i, Fintype (P i)] [∀ i, DecidableEq (P i)]

def concatenate {X : Type*} (w : ∀ i, P i → X) : (Σ i, P i) → X :=
  fun p => w p.1 p.2

def concatenateEquiv (X : Type*) : (∀ i, P i → X) ≃ ((Σ i, P i) → X) where
  toFun := concatenate P
  invFun := fun w i p => w ⟨i, p⟩
  left_inv := by intro w; rfl
  right_inv := by intro w; rfl

section Windows

variable {A : Type*} [Fintype A] [DecidableEq A]

omit [DecidableEq I] [∀ index, DecidableEq (P index)] [Fintype A] in
theorem wordPopulation_concatenate (w : ∀ i, P i → A) (a : A) :
    wordPopulation (concatenate P w) a = ∑ i, wordPopulation (w i) a := by
  let e : {p : (Σ i, P i) // concatenate P w p = a} ≃
      (Σ i, {p : P i // w i p = a}) :=
    { toFun := fun p => ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
      invFun := fun p => ⟨⟨p.1, p.2.val⟩, p.2.property⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  exact (Fintype.card_congr e).trans Fintype.card_sigma

omit [DecidableEq I] [∀ index, DecidableEq (P index)] [Fintype A] in
theorem empiricalLaw_concatenate (w : ∀ i, P i → A) (a : A) :
    empiricalLaw (concatenate P w) a =
      ∑ i, ((Fintype.card (P i) : ℝ) / Fintype.card (Σ i, P i)) *
        empiricalLaw (w i) a := by
  rw [empiricalLaw, wordPopulation_concatenate, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Fintype.card (P i) = 0
  · have hp : wordPopulation (w i) a = 0 := by
      have hle := Fintype.card_subtype_le (fun p : P i => w i p = a)
      change wordPopulation (w i) a ≤ Fintype.card (P i) at hle
      omega
    simp [hi, hp]
  · have hi' : (Fintype.card (P i) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hi
    simp only [empiricalLaw, div_eq_mul_inv]
    calc
      (wordPopulation (w i) a : ℝ) * (Fintype.card (Σ i, P i) : ℝ)⁻¹ =
          (wordPopulation (w i) a : ℝ) * (Fintype.card (Σ i, P i) : ℝ)⁻¹ *
            ((Fintype.card (P i) : ℝ) * (Fintype.card (P i) : ℝ)⁻¹) := by
        rw [mul_inv_cancel₀ hi', mul_one]
      _ = (Fintype.card (P i) : ℝ) * (Fintype.card (Σ i, P i) : ℝ)⁻¹ *
          ((wordPopulation (w i) a : ℝ) * (Fintype.card (P i) : ℝ)⁻¹) := by ring

def partWindows (ν : A → ℝ) (η : I → ℝ) (w : ∀ i, P i → A) : Prop :=
  ∀ i, 0 < Fintype.card (P i) → typeWindow ν (η i) (w i)

omit [DecidableEq I] [∀ index, DecidableEq (P index)] [Fintype A] in
theorem typeWindow_concatenate (ν : A → ℝ) (η : ℝ) (ηpart : I → ℝ)
    (hη : 0 ≤ η) (hwidth : ∀ i, ηpart i ≤ η)
    (hsize : 0 < Fintype.card (Σ i, P i)) (w : ∀ i, P i → A)
    (hw : partWindows P ν ηpart w) : typeWindow ν η (concatenate P w) := by
  intro a
  let mass : I → ℝ := fun i => (Fintype.card (P i) : ℝ) / Fintype.card (Σ i, P i)
  let law : I → ℝ := fun i =>
    if Fintype.card (P i) = 0 then ν a else empiricalLaw (w i) a
  have hm : ∀ i, 0 ≤ mass i := fun i => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsum : ∑ i, mass i = 1 := by
    dsimp [mass]
    rw [← Finset.sum_div, ← Nat.cast_sum, ← Fintype.card_sigma]
    exact div_self (by exact_mod_cast (Nat.ne_of_gt hsize))
  have hl : ∀ i, |law i - ν a| ≤ η := by
    intro i
    by_cases hi : Fintype.card (P i) = 0
    · simpa [law, hi] using hη
    · simpa only [law, ite_eq_right hi] using
        (hw i (Nat.pos_of_ne_zero hi) a).trans (hwidth i)
  have heq : empiricalLaw (concatenate P w) a = ∑ i, mass i * law i := by
    rw [empiricalLaw_concatenate]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : Fintype.card (P i) = 0 <;> simp [mass, law, hi]
  rw [heq]
  exact weighted_window mass law (ν a) η hm hsum hl

omit [DecidableEq I] [∀ index, DecidableEq (P index)] [Fintype A] in
theorem statisticWindow_concatenate {X : Type*} (statistic : X → A)
    (ν : A → ℝ) (η : ℝ) (ηpart : I → ℝ)
    (hη : 0 ≤ η) (hwidth : ∀ i, ηpart i ≤ η)
    (hsize : 0 < Fintype.card (Σ i, P i)) (w : ∀ i, P i → X)
    (hw : partWindows P ν ηpart (fun i => statistic ∘ w i)) :
    typeWindow ν η (statistic ∘ concatenate P w) := by
  exact typeWindow_concatenate P ν η ηpart hη hwidth hsize
    (fun index => statistic ∘ w index) hw

end Windows

def positionsOfCounts (count : I → ℕ) (n : ℕ) (hsum : ∑ i, count i = n) :
    Fin n ≃ (Σ i, Fin (count i)) :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_sigma, hsum])

theorem typeWindow_reindex {A Q R : Type*}
    [Fintype A] [DecidableEq A] [Fintype Q] [DecidableEq Q]
    [Fintype R] [DecidableEq R]
    (ν : A → ℝ) (η : ℝ) (w : R → A) (e : Q ≃ R) :
    typeWindow ν η (w ∘ e) ↔ typeWindow ν η w := by
  simp only [typeWindow, empiricalLaw, wordPopulation_reindex, Fintype.card_congr e]

omit [DecidableEq I] [∀ index, DecidableEq (P index)] in
theorem statisticWindow_concatenate_at {A X Q : Type*}
    [Fintype A] [DecidableEq A] [Fintype Q] [DecidableEq Q]
    (e : Q ≃ (Σ i, P i)) (statistic : X → A)
    (ν : A → ℝ) (η : ℝ) (ηpart : I → ℝ)
    (hη : 0 ≤ η) (hwidth : ∀ i, ηpart i ≤ η)
    (hsize : 0 < Fintype.card (Σ i, P i)) (w : ∀ i, P i → X)
    (hw : partWindows P ν ηpart (fun i => statistic ∘ w i)) :
    typeWindow ν η (statistic ∘ (concatenate P w ∘ e)) := by
  change typeWindow ν η ((statistic ∘ concatenate P w) ∘ e)
  exact (typeWindow_reindex ν η _ e).mpr
    (statisticWindow_concatenate P statistic ν η ηpart hη hwidth hsize w hw)

section Coefficients

variable {F X Y Z : Type*} [CommSemiring F]
    [Fintype X] [Fintype Y] [Fintype Z]

def repeated (Q : Type*) [Fintype Q] (T : Tensor F X Y Z) :
    Tensor F (Q → X) (Q → Y) (Q → Z) := fun x y z => ∏ p, T (x p) (y p) (z p)

def allParts {U : Type*} (keep : ∀ i, (P i → U) → Prop) (w : ∀ i, P i → U) : Prop :=
  ∀ i, keep i (w i)

def subdivisionMatrix {U : Type*} (keep : ∀ i, (P i → U) → Prop) :
    (∀ i, P i → U) → ((Σ i, P i) → U) → F :=
  fun w v => if v = concatenate P w ∧ allParts P keep w then 1 else 0

theorem subdivisionMatrix_apply (T : Tensor F ((Σ i, P i) → X)
    ((Σ i, P i) → Y) ((Σ i, P i) → Z))
    (keepX : ∀ i, (P i → X) → Prop) (keepY : ∀ i, (P i → Y) → Prop)
    (keepZ : ∀ i, (P i → Z) → Prop)
    (x : ∀ i, P i → X) (y : ∀ i, P i → Y) (z : ∀ i, P i → Z) :
    Tensor.restrict (subdivisionMatrix P keepX) (subdivisionMatrix P keepY)
      (subdivisionMatrix P keepZ) T x y z =
        if allParts P keepX x ∧ allParts P keepY y ∧ allParts P keepZ z then
          T (concatenate P x) (concatenate P y) (concatenate P z) else 0 := by
  by_cases hx : allParts P keepX x <;>
    by_cases hy : allParts P keepY y <;>
    by_cases hz : allParts P keepZ z <;>
    simp [Tensor.restrict, subdivisionMatrix, hx, hy, hz, ite_mul, mul_ite]

theorem restrict_received (T : Tensor F X Y Z)
    (receivedX : ((Σ i, P i) → X) → Prop)
    (receivedY : ((Σ i, P i) → Y) → Prop)
    (receivedZ : ((Σ i, P i) → Z) → Prop)
    (keepX : ∀ i, (P i → X) → Prop) (keepY : ∀ i, (P i → Y) → Prop)
    (keepZ : ∀ i, (P i → Z) → Prop)
    (hx : ∀ x, allParts P keepX x → receivedX (concatenate P x))
    (hy : ∀ y, allParts P keepY y → receivedY (concatenate P y))
    (hz : ∀ z, allParts P keepZ z → receivedZ (concatenate P z)) :
    Tensor.restrict (subdivisionMatrix P keepX) (subdivisionMatrix P keepY)
      (subdivisionMatrix P keepZ)
      (ExactRecovery.delete (repeated (Σ i, P i) T) receivedX receivedY receivedZ) =
        fun x y z => ∏ i, ExactRecovery.delete (repeated (P i) T)
          (keepX i) (keepY i) (keepZ i) (x i) (y i) (z i) := by
  funext x y z
  rw [subdivisionMatrix_apply]
  simp only [ExactRecovery.delete, Fintype.prod_ite_zero, forall_and]
  by_cases h : allParts P keepX x ∧ allParts P keepY y ∧ allParts P keepZ z
  · have hX := hx x h.1
    have hY := hy y h.2.1
    have hZ := hz z h.2.2
    have hp : (∀ i, keepX i (x i)) ∧ (∀ i, keepY i (y i)) ∧
        (∀ i, keepZ i (z i)) := h
    simp only [ite_eq_left h, ite_eq_left hp, hX, hY, hZ, and_self, ite_true]
    simp only [repeated, concatenate, Fintype.prod_sigma]
  · simp only [allParts] at h
    simp [allParts, h]

def subdivisionMatrixAt {U Q : Type*} (e : Q ≃ (Σ i, P i))
    (keep : ∀ i, (P i → U) → Prop) :
    (∀ i, P i → U) → (Q → U) → F :=
  fun w v => if v = concatenate P w ∘ e ∧ allParts P keep w then 1 else 0

omit [DecidableEq I] [∀ index, DecidableEq (P index)] in
theorem restrict_received_at {Q : Type*} [Fintype Q] [DecidableEq Q]
    (e : Q ≃ (Σ i, P i)) (T : Tensor F X Y Z)
    (receivedX : (Q → X) → Prop) (receivedY : (Q → Y) → Prop)
    (receivedZ : (Q → Z) → Prop)
    (keepX : ∀ i, (P i → X) → Prop) (keepY : ∀ i, (P i → Y) → Prop)
    (keepZ : ∀ i, (P i → Z) → Prop)
    (hx : ∀ x, allParts P keepX x → receivedX (concatenate P x ∘ e))
    (hy : ∀ y, allParts P keepY y → receivedY (concatenate P y ∘ e))
    (hz : ∀ z, allParts P keepZ z → receivedZ (concatenate P z ∘ e)) :
    Tensor.restrict (subdivisionMatrixAt P e keepX) (subdivisionMatrixAt P e keepY)
      (subdivisionMatrixAt P e keepZ)
      (ExactRecovery.delete (repeated Q T) receivedX receivedY receivedZ) =
        fun x y z => ∏ i, ExactRecovery.delete (repeated (P i) T)
          (keepX i) (keepY i) (keepZ i) (x i) (y i) (z i) := by
  funext x y z
  have hcollapse : Tensor.restrict (subdivisionMatrixAt P e keepX)
      (subdivisionMatrixAt P e keepY) (subdivisionMatrixAt P e keepZ)
      (ExactRecovery.delete (repeated Q T) receivedX receivedY receivedZ) x y z =
        if allParts P keepX x ∧ allParts P keepY y ∧ allParts P keepZ z then
          ExactRecovery.delete (repeated Q T) receivedX receivedY receivedZ
            (concatenate P x ∘ e) (concatenate P y ∘ e) (concatenate P z ∘ e) else 0 := by
    by_cases hx : allParts P keepX x <;>
      by_cases hy : allParts P keepY y <;>
      by_cases hz : allParts P keepZ z <;>
      simp [Tensor.restrict, subdivisionMatrixAt, hx, hy, hz, ite_mul, mul_ite]
  rw [hcollapse]
  simp only [ExactRecovery.delete, Fintype.prod_ite_zero, forall_and]
  by_cases h : allParts P keepX x ∧ allParts P keepY y ∧ allParts P keepZ z
  · have hX := hx x h.1
    have hY := hy y h.2.1
    have hZ := hz z h.2.2
    have hp : (∀ i, keepX i (x i)) ∧ (∀ i, keepY i (y i)) ∧
        (∀ i, keepZ i (z i)) := h
    simp only [ite_eq_left h, ite_eq_left hp, hX, hY, hZ, and_self, ite_true, repeated,
      Function.comp_apply]
    have hprod := Equiv.prod_comp e (fun p =>
      T (concatenate P x p) (concatenate P y p) (concatenate P z p))
    simpa only [concatenate, Fintype.prod_sigma] using hprod
  · simp only [allParts] at h
    simp [allParts, h]

end Coefficients

end MatrixMultiplication.Subdivision

end
end

end MatrixAllFields

end OAI
