import OAI.NumberTheory.Ostmann.Characters.QuartetExpansion
import OAI.NumberTheory.Ostmann.Tree.QuartetPairMajorant
import OAI.NumberTheory.Ostmann.ZeroDensity.PairDensity

namespace OAI

/-! # The second moment of the zero-extended bottom-pair value -/

namespace Ostmann

open scoped BigOperators

@[simp] theorem fieldBottomPairValue_zero_difference {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (t : ZMod p) : fieldBottomPairValue g 0 t = 0 := by
  simp [fieldBottomPairValue]

@[simp] theorem fieldBottomPairValue_zero_ratio {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : ZMod p) : fieldBottomPairValue g d 0 = 0 := by
  by_cases hd : d = 0 <;> simp [fieldBottomPairValue, hd]

theorem fieldBottomPairValue_units {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d t : (ZMod p)ˣ) :
    fieldBottomPairValue g d t = bottomPairValue g d t := by
  simp [fieldBottomPairValue, Units.ne_zero, Units.mk0_val]

noncomputable def fieldPairMoment {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : ZMod p) : ℝ :=
  (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
    ∑ t : (ZMod p)ˣ, ‖fieldBottomPairValue g d t‖ ^ 2

@[simp] theorem fieldPairMoment_zero {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) : fieldPairMoment g 0 = 0 := by
  simp [fieldPairMoment]

theorem fieldPairMoment_nonneg {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (d : ZMod p) : 0 ≤ fieldPairMoment g d := by
  unfold fieldPairMoment
  positivity

theorem fieldPairMoment_eq_difference {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0) (d : (ZMod p)ˣ) :
    fieldPairMoment g d =
      differenceMajorant (fun x => ‖g x‖ ^ 2) (fun x => ‖g x‖ ^ 2) d := by
  unfold fieldPairMoment differenceMajorant differenceMoment
  simp_rw [fieldBottomPairValue_units]
  congr 1
  have h := pair_ratio_sum_eq d (fun x => ‖g x‖ ^ 2) (fun x => ‖g x‖ ^ 2)
    (by simp [hg]) (by simp [hg])
  convert h using 1
  apply Finset.sum_congr rfl
  intro t _
  unfold bottomPairValue
  split_ifs <;> simp [mul_pow]

theorem fieldPairMoment_mean_le {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (hg : g 0 = 0)
    (henergy : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ)) :
    (∑ d : ZMod p, fieldPairMoment g d) / (Fintype.card (ZMod p)ˣ : ℝ) ≤
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by
  rw [← sum_units_eq_sum_of_zero _ (fieldPairMoment_zero g)]
  simp_rw [fieldPairMoment_eq_difference g hg]
  apply (mean_differenceMajorant_le (fun x => ‖g x‖ ^ 2) (fun x => ‖g x‖ ^ 2)
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)).trans
  rw [← pow_two]
  apply pow_le_pow_left₀ (by positivity)
  exact div_le_div_of_nonneg_right henergy (Nat.cast_nonneg _)

end Ostmann

end OAI
