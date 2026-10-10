import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

/-! # Finite mass accounting for the terminal far and near regions -/

namespace ContingencyTables.TerminalMassCover

open scoped BigOperators Classical

variable {X C : Type*} [Fintype X] [Fintype C]

/-- A finite union estimate retaining the feasible unit summands exactly.
The application proves the cover from the original root and tree penalties. -/
theorem mass_le_cover (w : X → ℝ) (feasible far : X → Prop) (near : C → X → Prop)
    (hw : ∀ x,0 ≤ w x) (hunit : ∀ x,feasible x → w x=1)
    (hcover : ∀ x,0 < w x → ¬feasible x → far x ∨ ∃ c,near c x) :
    (∑ x,w x) ≤ (∑ x,if feasible x then (1:ℝ) else 0)+
      (∑ x,if far x then w x else 0)+∑ c,∑ x,if near c x then w x else 0 := by
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hn : 0 ≤ ∑ c,if near c x then w x else 0 := by
    apply Finset.sum_nonneg
    intro c _
    split_ifs <;> first | exact hw x | exact le_rfl
  have hf : 0 ≤ if far x then w x else 0 := by
    split_ifs <;> first | exact hw x | exact le_rfl
  by_cases hx : feasible x
  · simp only [hx,ite_true]
    calc
      w x = 1 := hunit x hx
      _ ≤ 1+(if far x then w x else 0)+(∑ c,if near c x then w x else 0) := by linarith
  · simp only [hx,ite_false,zero_add]
    by_cases hp : 0 < w x
    · rcases hcover x hp hx with hf'|⟨c,hc⟩
      · rw [ite_eq_left hf']
        linarith
      · have hs := Finset.single_le_sum
          (f := fun c => if near c x then w x else 0)
          (fun c _ => by split_ifs <;> first | exact hw x | exact le_rfl)
          (Finset.mem_univ c)
        simp only [hc,ite_true] at hs
        linarith
    · have hz : w x=0 := le_antisymm (le_of_not_gt hp) (hw x)
      simp only [hz,ite_self,Finset.sum_const_zero,zero_add,le_refl]

/-- The manuscript's final conversion from a small fraction of the
normalizer to a relative error against the exact table count. -/
theorem relative_count_bound (Z M epsilon : ℝ) (hZ : 0 ≤ Z)
    (he : 0 < epsilon) (he1 : epsilon < 1) (hZM : Z ≤ M)
    (hbad : M ≤ Z+(epsilon/64)*M) :
    Z ≤ M ∧ M ≤ (1+epsilon/32)*Z := by
  refine ⟨hZM,?_⟩
  have hM : 0 ≤ M := hZ.trans hZM
  have hscaled : (1-epsilon/64)*M ≤ Z := by linarith
  have hfactor : 0 ≤ 1+epsilon/32 := by positivity
  have hh := mul_le_mul_of_nonneg_left hscaled hfactor
  have hcoef : 1 ≤ (1+epsilon/32)*(1-epsilon/64) := by
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr he1.le)]
  have hmono := mul_le_mul_of_nonneg_right hcoef hM
  nlinarith

end ContingencyTables.TerminalMassCover

end OAI
