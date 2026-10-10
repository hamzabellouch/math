import OAI.NumberTheory.Ostmann.Construction.GraphCopySchedule
import OAI.NumberTheory.Ostmann.Construction.TransferLocalPhases

namespace OAI

/-! # Frequency-independent multipliers of the regular copied rows -/

namespace Ostmann

open scoped ComplexConjugate

/-- Copying never conjugates the underlying Dirichlet character. -/
def copyScheduleOrigin {I : Type*} : (n : ℕ) → CopyScheduleVertex I n → I
  | 0, i => i
  | n + 1, .inl (_, i) => copyScheduleOrigin n i
  | n + 1, .inr i => copyScheduleOrigin n i

@[simp] theorem copyScheduleOrigin_path {I : Type*} (n : ℕ) (t : Fin n → Bool) (i : I) :
    copyScheduleOrigin n (copySchedulePath n t i) = i := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih _

/-- All frequency dependence of a regular unary is its current root power. -/
noncomputable def regularUnary {p : ℕ} (χ : DirichletCharacter ℂ p)
    (κ : ℂ) (ε : ℤ) (v : ZMod p) : ℂ := κ * χ v ^ (-ε)

noncomputable def regularCopiedMultiplier {p : ℕ} (χ : DirichletCharacter ℂ p)
    (κ : ℂ) (ε : ℤ) (b : Bool) : ℂ :=
  if b then κ else conj κ * χ (-1) ^ (-ε)

theorem regularUnary_left {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (κ : ℂ) (ε : ℤ) (v s : ZMod p) (hv : v ≠ 0) :
    regularUnary χ κ ε v * χ (v / s) ^ ε =
      regularUnary χ (regularCopiedMultiplier χ κ ε true) (transferCopySign true * ε) s := by
  simp only [regularUnary, regularCopiedMultiplier, ite_true, transferCopySign, one_mul]
  rw [mul_assoc, transfer_regular_unary χ v s hv ε]

theorem regularUnary_right {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (κ : ℂ) (ε : ℤ) (w s : ZMod p) (hw : w ≠ 0) :
    conj (regularUnary χ κ ε w) * χ (-w / s) ^ (-ε) =
      regularUnary χ (regularCopiedMultiplier χ κ ε false) (transferCopySign false * ε) s := by
  have he : χ (-w / s) = χ (-1) * χ (w / s) := by
    rw [show -w / s = (-1 : ZMod p) * (w / s) by ring, map_mul]
  simp only [regularUnary, regularCopiedMultiplier, Bool.false_eq_true, ite_false,
    transferCopySign, neg_one_mul, neg_neg, map_mul (starRingEnd ℂ),
    conjugate_character_power, he, mul_zpow]
  calc
    _ = (conj κ * χ (-1) ^ (-ε)) * (χ w ^ ε * χ (w / s) ^ (-ε)) := by ring
    _ = _ := by
      have hu := transfer_regular_unary χ w s hw (-ε)
      simp only [neg_neg] at hu
      rw [hu]

/-- This multiplier is constructed from the role character, original Gauss
multiplier, and copy signs alone; it contains no frequency parameters. -/
noncomputable def scheduledWordMultiplier {p : ℕ} (χ : DirichletCharacter ℂ p) (κ : ℂ) :
    (n : ℕ) → (Fin n → Bool) → ℂ
  | 0, _ => κ
  | n + 1, t => regularCopiedMultiplier χ
      (scheduledWordMultiplier χ κ n (fun j => t j.castSucc))
      (finalCopyParity (fun j => t j.castSucc)) (t (Fin.last n))

theorem scheduledWordMultiplier_snoc {p : ℕ} (χ : DirichletCharacter ℂ p) (κ : ℂ)
    (n : ℕ) (t : Fin n → Bool) (b : Bool) :
    scheduledWordMultiplier χ κ (n + 1) (Fin.snoc t b) =
      regularCopiedMultiplier χ (scheduledWordMultiplier χ κ n t) (finalCopyParity t) b := by
  simp only [scheduledWordMultiplier, Fin.snoc_castSucc, Fin.snoc_last]

theorem regularCopiedMultiplier_norm {p : ℕ} (χ : DirichletCharacter ℂ p)
    (κ : ℂ) (hκ : ‖κ‖ = 1) (ε : ℤ) (b : Bool) :
    ‖regularCopiedMultiplier χ κ ε b‖ = 1 := by
  cases b
  · simp only [regularCopiedMultiplier, Bool.false_eq_true, ite_false, norm_mul, norm_zpow]
    have hunit : IsUnit (-1 : ZMod p) := isUnit_one.neg
    obtain ⟨u, hu⟩ := hunit
    rw [← hu, χ.unit_norm_eq_one, one_zpow]
    change ‖conj κ‖ * 1 = 1
    rw [Complex.norm_conj, hκ, one_mul]
  · exact hκ

theorem scheduledWordMultiplier_norm {p : ℕ} (χ : DirichletCharacter ℂ p)
    (κ : ℂ) (hκ : ‖κ‖ = 1) (n : ℕ) (t : Fin n → Bool) :
    ‖scheduledWordMultiplier χ κ n t‖ = 1 := by
  induction n with
  | zero => exact hκ
  | succ n ih => exact regularCopiedMultiplier_norm χ _ (ih _) _ _

/-- The exact regular unary recurrence at every word copy. -/
theorem scheduledWordUnary_step {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (κ : ℂ) (n : ℕ) (t : Fin n → Bool)
    (b : Bool) (v w s : ZMod p) (hv : v ≠ 0) (hw : w ≠ 0) :
    (if b then
        regularUnary χ (scheduledWordMultiplier χ κ n t) (finalCopyParity t) v *
          χ (v / s) ^ finalCopyParity t
      else
        conj (regularUnary χ (scheduledWordMultiplier χ κ n t) (finalCopyParity t) w) *
          χ (-w / s) ^ (-finalCopyParity t)) =
      regularUnary χ (scheduledWordMultiplier χ κ (n + 1) (Fin.snoc t b))
        (finalCopyParity (Fin.snoc t b)) s := by
  rw [scheduledWordMultiplier_snoc, finalCopyParity_snoc]
  cases b
  · exact regularUnary_right χ _ _ w s hw
  · exact regularUnary_left χ _ _ v s hv

end Ostmann

end OAI
