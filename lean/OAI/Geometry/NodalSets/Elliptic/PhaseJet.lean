import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace OAI

namespace Yau
noncomputable section

def contactEta (a b h00 h11 : ℝ) : ℝ :=
  (a ^ 2 * h00 + b ^ 2 * h11) / (a ^ 2 + b ^ 2)

theorem contactEta_pos {a b h00 h11 : ℝ} (ha : a ≠ 0)
    (h : 0 < a ^ 2 * h00 + b ^ 2 * h11) :
    0 < contactEta a b h00 h11 := by
  unfold contactEta
  apply div_pos h
  have := sq_pos_of_ne_zero ha
  positivity

theorem contactEta_compatibility {a b h00 h11 : ℝ} (ha : a ≠ 0) :
    a ^ 2 * (h00 - contactEta a b h00 h11) +
      b ^ 2 * (h11 - contactEta a b h00 h11) = 0 := by
  have hd : a ^ 2 + b ^ 2 ≠ 0 := by
    have := sq_pos_of_ne_zero ha
    positivity
  unfold contactEta
  field_simp
  ring

def imaginaryHessian (a b : ℝ) (H : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ := fun i j ↦
  if i = 0 then -(b / a) * H 1 j
  else if i = 1 then (a / b) * H 0 j
  else if j = 0 then -(b / a) * H 1 i
  else if j = 1 then (a / b) * H 0 i
  else 0

theorem imaginaryHessian_symmetric {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {H : Matrix (Fin 4) (Fin 4) ℝ}
    (hc : a ^ 2 * H 0 0 + b ^ 2 * H 1 1 = 0) :
    ∀ i j, imaginaryHessian a b H i j = imaginaryHessian a b H j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [imaginaryHessian]
  all_goals field_simp
  all_goals nlinarith [hc]

theorem imaginaryHessian_contractions {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (H : Matrix (Fin 4) (Fin 4) ℝ) (j : Fin 4) :
    b * imaginaryHessian a b H 1 j = a * H 0 j ∧
    a * imaginaryHessian a b H 0 j = -b * H 1 j := by
  simp [imaginaryHessian]
  constructor <;> field_simp

theorem exists_imaginaryHessian {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (H : Matrix (Fin 4) (Fin 4) ℝ)
    (hc : a ^ 2 * H 0 0 + b ^ 2 * H 1 1 = 0) :
    ∃ K : Matrix (Fin 4) (Fin 4) ℝ,
      (∀ i j, K i j = K j i) ∧
      ∀ j, b * K 1 j = a * H 0 j ∧ a * K 0 j = -b * H 1 j := by
  exact ⟨imaginaryHessian a b H, imaginaryHessian_symmetric ha hb hc,
    imaginaryHessian_contractions ha hb H⟩

end
end Yau

end OAI
