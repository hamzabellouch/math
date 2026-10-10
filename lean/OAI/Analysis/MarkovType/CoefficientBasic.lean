import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

def CoefficientBasic (K : ℝ) (x : Fin n → E) : Prop :=
  ∀ a : Fin n → ℝ, ∀ k : ℕ, k ≤ n →
    ‖∑ i : Fin n, if i.val < k then a i • x i else 0‖ ≤
      K * ‖∑ i : Fin n, a i • x i‖

abbrev CoefficientMonotone (x : Fin n → E) : Prop := CoefficientBasic 1 x

theorem CoefficientBasic.smul {K : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (c : Fin n → ℝ) :
    CoefficientBasic K (fun i => c i • x i) := by
  intro a k hk
  simpa only [smul_smul] using hx (fun i => a i * c i) k hk

theorem CoefficientBasic.mono {K L : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (hKL : K ≤ L) : CoefficientBasic L x := by
  intro a k hk
  exact (hx a k hk).trans (mul_le_mul_of_nonneg_right hKL (norm_nonneg _))

theorem coefficientBasic_zero (K : ℝ) (n : ℕ) :
    CoefficientBasic K (fun _ : Fin n => (0 : E)) := by
  intro a k hk
  simp

theorem CoefficientBasic.norm_prefix_le {K : ℝ} {x : Fin n → E}
    (hx : CoefficientBasic K x) (k : ℕ) (hk : k ≤ n) :
    ‖∑ i : Fin n, if i.val < k then x i else 0‖ ≤ K * ‖∑ i : Fin n, x i‖ := by
  simpa only [one_smul] using hx (fun _ => 1) k hk

end MarkovSuperreflexivity

end OAI
