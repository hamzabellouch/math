import Mathlib
import OAI.Probability.BinarySweep.Trajectories.PathSign

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
attribute [local instance] Classical.propDecidable
variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma exists_untouched_line (j : Fin b) (hh : h<Fintype.card (GridOutside bits j)) :
    ∃y : GridOutside bits j, lineHoles H j y=0 := by
  by_contra hn
  push Not at hn
  have he := Finset.sum_le_sum (s:=Finset.univ)
    (fun y _ => Nat.one_le_iff_ne_zero.mpr (hn y))
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,sum_lineHoles] at he
  omega

lemma signed_path_weight_zero_sparse (z : ℝ) (j : Fin b) (hj : 0<bits j)
    (hh : h<Fintype.card (GridOutside bits j)) :
    (∑g : GridChoices bits, if pathEvent H g then
      gridWeight bits z g*realSign (gridSweep bits g) else 0)=0 := by
  obtain ⟨y,hy⟩ := exists_untouched_line H j hh
  exact signed_path_weight_zero_empty H z j hj y hy

lemma two_outside_embedding {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ↪ Y) (h : Fintype.card X+1<Fintype.card Y) :
    ∃u v : Y, u≠v ∧ u∉Set.range e ∧ v∉Set.range e := by
  let S := {y : Y // y∉Set.range e}
  have hc : Fintype.card S=Fintype.card Y-Fintype.card X := by
    dsimp only [S]
    rw [Fintype.card_subtype_compl,Fintype.card_range]
  have hS : 1<Fintype.card S := by omega
  have : Nontrivial S := Fintype.one_lt_card_iff_nontrivial.mp hS
  obtain ⟨u,v,huv⟩ := exists_pair_ne S
  exact ⟨u.val,v.val,(fun he => huv (Subtype.ext he)),u.property,v.property⟩

lemma exists_line_two_free (j : Fin b)
    (hh : h+Fintype.card (GridOutside bits j)<gridSize bits) :
    ∃y : GridOutside bits j, ∃u v : Slot (bits j), u≠v ∧
      u∉Set.range (lineOutput H j y) ∧ v∉Set.range (lineOutput H j y) := by
  have hfull : Fintype.card (GridOutside bits j)*2^bits j=gridSize bits := by
    have he := Fintype.card_congr (Equiv.piSplitAt j (fun i => Slot (bits i)))
    change Fintype.card (GridSlot bits)=Fintype.card (Slot (bits j) × GridOutside bits j) at he
    have hs : Fintype.card (Slot (bits j))=2^bits j := by simp [Slot]
    have hg : Fintype.card (GridSlot bits)=gridSize bits := by simp [GridSlot,gridSize,Slot]
    simpa only [Fintype.card_prod,hs,hg,mul_comm] using he.symm
  have he : ∃y : GridOutside bits j, lineHoles H j y+1<2^bits j := by
    by_contra hn
    push Not at hn
    have hf := Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hn y)
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,
      mul_one,sum_lineHoles,hfull] at hf
    omega
  obtain ⟨y,hy⟩ := he
  refine ⟨y,?_⟩
  apply two_outside_embedding (lineOutput H j y)
  have hc : Fintype.card (LinePaths H j y)=lineHoles H j y := by
    unfold LinePaths lineHoles
    congr 1
  rw [hc]
  simpa [Slot] using hy

lemma signed_path_weight_zero_few (j : Fin b)
    (hh : h+Fintype.card (GridOutside bits j)<gridSize bits) :
    (∑g : GridChoices bits, if pathEvent H g then
      gridWeight bits 0 g*realSign (gridSweep bits g) else 0)=0 := by
  obtain ⟨y,u,v,huv,hu,hv⟩ := exists_line_two_free H j hh
  exact signed_path_weight_zero_uniform H j y huv hu hv

end BinaryCoordinateSweeps

end

end OAI
