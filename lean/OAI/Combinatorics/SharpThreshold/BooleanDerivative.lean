import OAI.Combinatorics.SharpThreshold.Probability
import OAI.Combinatorics.SharpThreshold.InfluenceReindex

namespace OAI

universe u

noncomputable section
namespace Problem313

@[simp] theorem boolReal_sub_abs (a b : Bool) :
    |boolReal a - boolReal b| = if a ≠ b then 1 else 0 := by
  cases a <;> cases b <;> norm_num [boolReal]

@[simp] theorem boolReal_sub_sq (a b : Bool) :
    (boolReal a - boolReal b) ^ 2 = if a ≠ b then 1 else 0 := by
  cases a <;> cases b <;> norm_num [boolReal]

@[simp] theorem boolReal_sub_fourth (a b : Bool) :
    (boolReal a - boolReal b) ^ 4 = if a ≠ b then 1 else 0 := by
  cases a <;> cases b <;> norm_num [boolReal]

theorem boolReal_sub_mem (a b : Bool) :
    boolReal a - boolReal b = -1 ∨ boolReal a - boolReal b = 0 ∨
      boolReal a - boolReal b = 1 := by
  cases a <;> cases b <;> norm_num [boolReal]

theorem boolReal_sub_abs_le_one (a b : Bool) : |boolReal a - boolReal b| ≤ 1 := by
  rw [boolReal_sub_abs]
  split_ifs <;> norm_num

namespace Reindex
variable {ι : Type u} [Fintype ι] [dι : DecidableEq ι]

theorem boolean_delta_abs_moment (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    (∑ x, weight p x * |boolReal (f (Function.update x i true)) -
      boolReal (f (Function.update x i false))|) = influence p f i := by
  classical
  have hd : dι = Classical.decEq ι := Subsingleton.elim _ _
  subst dι
  simp only [boolReal_sub_abs, mul_ite, mul_one, mul_zero, influence]

theorem boolean_delta_sq_moment (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    (∑ x, weight p x * (boolReal (f (Function.update x i true)) -
      boolReal (f (Function.update x i false))) ^ 2) = influence p f i := by
  classical
  have hd : dι = Classical.decEq ι := Subsingleton.elim _ _
  subst dι
  simp only [boolReal_sub_sq, mul_ite, mul_one, mul_zero, influence]

theorem boolean_delta_fourth_moment (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    (∑ x, weight p x * (boolReal (f (Function.update x i true)) -
      boolReal (f (Function.update x i false))) ^ 4) = influence p f i := by
  classical
  have hd : dι = Classical.decEq ι := Subsingleton.elim _ _
  subst dι
  simp only [boolReal_sub_fourth, mul_ite, mul_one, mul_zero, influence]

end Reindex
end Problem313

end

end OAI
