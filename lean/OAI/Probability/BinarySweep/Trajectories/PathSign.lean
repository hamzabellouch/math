import Mathlib
import OAI.Probability.BinarySweep.Conditional.Placement
import OAI.Probability.BinarySweep.FiniteLaws.AssignmentSign

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable

lemma realSign_gridLayer {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) (j : Fin b) :
    realSign (gridLayer bits g j)=∏y, realSign (g j y) := by
  simp [gridLayer,realSign,Equiv.Perm.sign_prodCongrLeft,map_prod]

lemma realSign_gridSweep {b : ℕ} (bits : Fin b → ℕ) (g : GridChoices bits) :
    realSign (gridSweep bits g)=∏j, ∏y, realSign (g j y) := by
  simp [gridSweep,map_list_prod,List.map_reverse,List.prod_reverse,
    List.map_ofFn,List.prod_ofFn,realSign_gridLayer]

lemma signed_path_integrand_factor {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) (g : GridChoices bits) :
    (if pathEvent H g then gridWeight bits z g*realSign (gridSweep bits g) else 0) =
      ∏j, ∏y, if Assigns (lineInput H j y) (lineOutput H j y) (g j y) then
        lineLaw (bits j) z (g j y)*realSign (g j y) else 0 := by
  rw [pathEvent_iff_assigns,realSign_gridSweep]
  simp only [Fintype.prod_ite_zero,Finset.prod_mul_distrib,gridWeight]
  split_ifs <;> rfl

lemma signed_path_weight_factor {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) :
    (∑g : GridChoices bits, if pathEvent H g then
      gridWeight bits z g*realSign (gridSweep bits g) else 0) =
      ∏j, ∏y, ∑σ : Equiv.Perm (Slot (bits j)),
        if Assigns (lineInput H j y) (lineOutput H j y) σ then
          lineLaw (bits j) z σ*realSign σ else 0 := by
  simp_rw [signed_path_integrand_factor H z]
  exact sum_prod_grid bits (fun j y σ =>
    if Assigns (lineInput H j y) (lineOutput H j y) σ then
      lineLaw (bits j) z σ*realSign σ else 0)

theorem signed_path_weight_zero_uniform {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (j : Fin b) (y : GridOutside bits j)
    {u v : Slot (bits j)} (huv : u≠v)
    (hu : u∉Set.range (lineOutput H j y)) (hv : v∉Set.range (lineOutput H j y)) :
    (∑g : GridChoices bits, if pathEvent H g then
      gridWeight bits 0 g*realSign (gridSweep bits g) else 0)=0 := by
  rw [signed_path_weight_factor]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply Finset.prod_eq_zero (Finset.mem_univ y)
  simpa only [lineLaw,sub_zero,one_mul,zero_mul,add_zero] using
    uniform_sign_assigns_zero (lineInput H j y) (lineOutput H j y) huv hu hv

theorem signed_path_weight_zero_empty {b h : ℕ} {bits : Fin b → ℕ}
    (H : PathFamily bits h) (z : ℝ) (j : Fin b) (hj : 0<bits j)
    (y : GridOutside bits j) (hy : lineHoles H j y=0) :
    (∑g : GridChoices bits, if pathEvent H g then
      gridWeight bits z g*realSign (gridSweep bits g) else 0)=0 := by
  rw [signed_path_weight_factor]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply Finset.prod_eq_zero (Finset.mem_univ y)
  have hz : IsEmpty (LinePaths H j y) := Fintype.card_eq_zero_iff.mp hy
  have ha (σ : Equiv.Perm (Slot (bits j))) :
      Assigns (lineInput H j y) (lineOutput H j y) σ := by
    intro a; exact isEmptyElim a
  simp only [ha,ite_true]
  exact lineLaw_sign_zero hj z

end BinaryCoordinateSweeps

end

end OAI
