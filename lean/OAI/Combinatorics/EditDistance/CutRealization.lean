import OAI.Combinatorics.EditDistance.CutModels
import OAI.Combinatorics.EditDistance.DirectSums

namespace OAI

/-!
# Realization of all finite-cut distances by one summable vector map
-/

namespace EditCutModel
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

noncomputable def Model.vector {X : Type*} (M : Model X) (x : X) : EditL1.L1 :=
  EditL1.pack (fun j : Option M.Index => match j with
    | none => 0
    | some i => lp.single (E := fun _ : ℕ => ℝ) 1 0 (if M.cut i x then M.weight i else 0))

lemma singleton_sub_norm (a b : ℝ) :
    ‖lp.single (E := fun _ : ℕ => ℝ) 1 0 a - lp.single (E := fun _ : ℕ => ℝ) 1 0 b‖ = |a-b| := by
  have he : lp.single (E := fun _ : ℕ => ℝ) 1 0 a - lp.single (E := fun _ : ℕ => ℝ) 1 0 b =
      lp.single (E := fun _ : ℕ => ℝ) 1 0 (a-b) := by
    ext i
    change (lp.single (E := fun _ : ℕ => ℝ) 1 0 a) i - (lp.single (E := fun _ : ℕ => ℝ) 1 0 b) i = (lp.single (E := fun _ : ℕ => ℝ) 1 0 (a-b)) i
    by_cases hi : i = 0
    · subst i
      simp only [lp.single_apply_self]
    · rw [lp.single_apply_ne (E := fun _ : ℕ => ℝ) 1 0 a hi,
        lp.single_apply_ne (E := fun _ : ℕ => ℝ) 1 0 b hi,
        lp.single_apply_ne (E := fun _ : ℕ => ℝ) 1 0 (a-b) hi,sub_self]
  rw [he,lp.norm_single (by norm_num)]
  exact Real.norm_eq_abs _

lemma Model.vector_distance {X : Type*} (M : Model X) (x y : X) :
    ‖M.vector x-M.vector y‖ = M.dist x y := by
  unfold Model.vector
  rw [EditL1.pack_distance,Fintype.sum_option]
  simp only [sub_self,norm_zero,zero_add]
  unfold Model.dist
  apply sum_congr rfl
  intro i _
  rw [singleton_sub_norm]
  cases hix : M.cut i x <;> cases hiy : M.cut i y <;>
    simp [sep, abs_of_nonneg (M.nonneg i)]

end EditCutModel

end OAI
