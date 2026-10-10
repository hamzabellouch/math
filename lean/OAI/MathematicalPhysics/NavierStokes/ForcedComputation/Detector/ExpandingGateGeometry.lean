import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingAddresses
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model

namespace OAI

/-! The three motions of the expanding address array are separated by
source columns, private rows, then target columns. Nonterminal transport
stays below the observation half-plane throughout every motion. -/

namespace ForcedComputation.ExpandingDetector
open ShearFlows

def gateCenter (S T : ℝ) (k target : ℕ) (terminal : Bool)
    (θ₁ θ₂ θ₃ : ℝ) : Plane :=
  ![(1 - θ₂) * S * k + θ₂ * T * target,
    -(1 - θ₁) * S + (θ₁ - θ₃) * (-((k : ℝ) + 2) * S) +
      θ₃ * (if terminal then T else -T)]

theorem natural_spacing {a b : ℕ} (hab : a ≠ b) :
    1 ≤ |(a : ℝ) - b| := by
  rcases lt_or_gt_of_ne hab with h | h
  · have hs : (a : ℝ) + 1 ≤ b := by exact_mod_cast Nat.add_one_le_iff.mpr h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hs : (b : ℝ) + 1 ≤ a := by exact_mod_cast Nat.add_one_le_iff.mpr h
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem gateCenter_initial (S T : ℝ) (k target : ℕ) (terminal : Bool) :
    gateCenter S T k target terminal 0 0 0 = ![S * k, -S] := by
  simp [gateCenter]

theorem gateCenter_final (S T : ℝ) (k target : ℕ) (terminal : Bool) :
    gateCenter S T k target terminal 1 1 1 =
      ![T * target, if terminal then T else -T] := by
  simp [gateCenter]

theorem gateCenter_separated {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    {a b a' b' : ℕ} (hab : a ≠ b) (htarget : a' ≠ b')
    (ha hb : Bool) (θ₁ θ₂ θ₃ : ℝ)
    (hslot : (θ₂ = 0 ∧ θ₃ = 0) ∨ (θ₁ = 1 ∧ θ₃ = 0) ∨
      (θ₁ = 1 ∧ θ₂ = 1)) :
    ∃ j : Fin 2, S ≤ |gateCenter S T a a' ha θ₁ θ₂ θ₃ j -
      gateCenter S T b b' hb θ₁ θ₂ θ₃ j| := by
  have hs := natural_spacing hab
  have ht := natural_spacing htarget
  rcases hslot with h | h | h
  · refine ⟨0, ?_⟩
    simp only [gateCenter, Matrix.cons_val_zero, h.1, sub_zero, zero_mul, add_zero,
      one_mul]
    rw [← mul_sub, abs_mul, abs_of_nonneg hS]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs hS
  · refine ⟨1, ?_⟩
    simp only [gateCenter, Matrix.cons_val_one, Matrix.cons_val_zero, h.1, h.2,
      sub_self, sub_zero, neg_zero, zero_mul, one_mul, zero_add, add_zero]
    have he : -((a : ℝ) + 2) * S - -((b : ℝ) + 2) * S = -((a : ℝ) - b) * S := by
      ring
    rw [he, abs_mul, abs_neg, abs_of_nonneg hS]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hS
  · refine ⟨0, ?_⟩
    simp only [gateCenter, Matrix.cons_val_zero, h.2, sub_self, zero_mul, zero_add,
      one_mul]
    rw [← mul_sub, abs_mul, abs_of_nonneg (hS.trans hST)]
    exact hST.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left ht (hS.trans hST))

theorem nonterminal_gate_below {S T : ℝ} (hS : 0 ≤ S) (hST : S ≤ T)
    (k target : ℕ) {θ₁ θ₂ θ₃ : ℝ}
    (h₃ : 0 ≤ θ₃) (h₃₁ : θ₃ ≤ θ₁) :
    gateCenter S T k target false θ₁ θ₂ θ₃ 1 ≤ -S := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hc₂ := mul_le_mul_of_nonneg_left
    (show -((k : ℝ) + 2) * S ≤ -S by nlinarith [mul_nonneg hk hS])
      (sub_nonneg.mpr h₃₁)
  have hc₃ := mul_le_mul_of_nonneg_left (neg_le_neg hST) h₃
  simp only [gateCenter, Matrix.cons_val_one, Matrix.cons_val_zero, Bool.false_eq_true,
    ite_false]
  nlinarith

end ForcedComputation.ExpandingDetector

end OAI
