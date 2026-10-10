import Mathlib
import OAI.Probability.BinarySweep.Conditional.ConditionalSpecht
import OAI.Probability.BinarySweep.FiniteLaws.RemainingSign
import OAI.Probability.BinarySweep.SparseBounds.SparseSignGeometry

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps

section
attribute [local instance] Classical.propDecidable
variable {b h h' k : ℕ} {bits : Fin b → ℕ} {H : PathFamily bits h} {H' : PathFamily bits h'}

lemma PathExtension.signed_restrict_zero (E : PathExtension H H') (z : ℝ)
    (hs : (∑g : GridChoices bits, if pathEvent H' g then
      gridWeight bits z g*realSign (gridSweep bits g) else 0)=0) :
    (∑g : ConditionalChoices H, if pathEvent H' g.val then
      conditionalChoiceWeight H z g*realSign (remainingPerm H g.val g.property) else 0)=0 := by
  obtain ⟨g₀,hg₀⟩ := pathEvent_nonempty H
  let a := realSign (remainingPerm H g₀ hg₀)/realSign (gridSweep bits g₀)
  have hs' : (∑g : ConditionalChoices H', gridWeight bits z g.val*realSign (gridSweep bits g.val))=0 := by
    have he := sum_dite_zero (pathEvent H')
      (fun g _ => gridWeight bits z g*realSign (gridSweep bits g))
    rw [←hs]
    refine Eq.trans ?_ he.symm
    apply Finset.sum_congr
    · ext g; simp only [Finset.mem_univ]
    intro g _; rfl
  calc
    _ = (a/conditionalNormalizer H z)*
        (∑g : ConditionalChoices H, if pathEvent H' g.val then
          gridWeight bits z g.val*realSign (gridSweep bits g.val) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : pathEvent H' g.val
      · rw [ite_eq_left hg,ite_eq_left hg,remaining_realSign_factor H g ⟨g₀,hg₀⟩]
        dsimp [a,conditionalChoiceWeight]
        ring
      · simp only [ite_eq_right hg,mul_zero]
    _ = (a/conditionalNormalizer H z)*
        (∑g : ConditionalChoices H', gridWeight bits z g.val*realSign (gridSweep bits g.val)) := by
      congr 1
      exact E.sum_restrict (fun g => gridWeight bits z g.val*realSign (gridSweep bits g.val))
    _ = 0 := by rw [hs',mul_zero]

variable (H)
def signedPlacementEntry (z : ℝ) (x : Placement H k 0) (y : Placement H k (Fin.last b)) : ℝ :=
  ∑g : ConditionalChoices H, if placementBijection H k g x=y then
    conditionalChoiceWeight H z g*realSign (remainingPerm H g.val g.property) else 0

lemma signedPlacementEntry_zero (z : ℝ) (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (hs : ∀g₀ : ConditionalChoices H,
      (∑g : GridChoices bits, if pathEvent (augmentByChoice H x g₀) g then
        gridWeight bits z g*realSign (gridSweep bits g) else 0)=0) :
    signedPlacementEntry H z x y=0 := by
  by_cases he : ∃g₀ : ConditionalChoices H, placementBijection H k g₀ x=y
  · obtain ⟨g₀,rfl⟩ := he
    have hz := (augmentByChoice_extension H x g₀).signed_restrict_zero z (hs g₀)
    refine Eq.trans ?_ hz
    unfold signedPlacementEntry
    apply Finset.sum_congr rfl
    intro g _
    simp only [placementEvent_iff_augmentation]
  · unfold signedPlacementEntry
    apply Finset.sum_eq_zero
    intro g _
    exact ite_eq_right (fun hg => he ⟨g,hg⟩)

theorem signedPlacementEntry_zero_many (z : ℝ) (j : Fin b) (hj : 0<bits j)
    (hh : h+k<Fintype.card (GridOutside bits j))
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    signedPlacementEntry H z x y=0 :=
  signedPlacementEntry_zero H z x y (fun g₀ =>
    signed_path_weight_zero_sparse (augmentByChoice H x g₀) z j hj hh)

theorem signedPlacementEntry_zero_few (j : Fin b)
    (hh : h+k+Fintype.card (GridOutside bits j)<gridSize bits)
    (x : Placement H k 0) (y : Placement H k (Fin.last b)) :
    signedPlacementEntry H 0 x y=0 :=
  signedPlacementEntry_zero H 0 x y (fun g₀ =>
    signed_path_weight_zero_few (augmentByChoice H x g₀) j hh)

end

open Young Irrep

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma signed_partialKernel_conditional (z : ℝ) (A : Finset (Fin k))
    (x y : Placement H k 0) :
    (∑a : Equiv.Perm (FreeSlot H 0), (conditionalGroupLaw H z a*realSign a:ℂ)*partialKernel A a y x)=
      (signedPlacementEntry H z (restrictPlacement H x A)
        (restrictPlacement H (placementIdentification H k y) A):ℂ) := by
  have he := conditionalGroupLaw_expectation H z (fun a => (realSign a:ℂ)*partialKernel A a y x)
  simp only [Complex.real_smul] at he
  simp only [mul_assoc]
  rw [he]
  unfold signedPlacementEntry
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr
  · ext g; simp only [Finset.mem_univ]
  intro g _
  simp only [partialKernel, partialKernel_event H g A x y, restrictPlacement_event]
  split_ifs <;> simp

lemma signed_centeredMatrix_zero (z : ℝ)
    (hh : ∀ l ≤ k, ∀x : Placement H l 0, ∀y : Placement H l (Fin.last b),
      signedPlacementEntry H z x y=0) :
    centeredMatrix (I:=Fin k) (gridSize bits)
      (fun a => (conditionalGroupLaw H z a*realSign a:ℂ))=0 := by
  ext y x
  simp only [centeredMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro A _
  rw [signed_partialKernel_conditional H z A x y]
  have hA : Fintype.card A ≤ k := by simpa using Finset.card_le_univ A
  rw [hh _ hA,Complex.ofReal_zero,mul_zero]

theorem conditional_signed_specht_one_le_zero (μ : YoungDiagram)
    (e : Cell μ ≃ FreeSlot H 0) (a : Tail μ ≃ Fin k) (z : ℝ)
    (hh : ∀ l ≤ k, ∀x : Placement H l 0, ∀y : Placement H l (Fin.last b),
      signedPlacementEntry H z x y=0) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g*realSign g:ℂ))) ≤ 0 := by
  rw [groupAverage_comp_slots]
  have hs : (gridSize bits:ℝ)≠0 := by exact_mod_cast (gridSize_pos bits).ne'
  have he := specht_moment_one_le_centered_matrix μ (gridSize bits) hs
    (fun g => (conditionalGroupLaw H z (e.permCongr g)*realSign (e.permCongr g):ℂ))
  have hr := centeredMatrix_hs_reindex a e (gridSize bits)
    (fun g => (conditionalGroupLaw H z (e.permCongr g)*realSign (e.permCongr g):ℂ))
  simp only [Equiv.apply_symm_apply] at hr
  rw [←hr,signed_centeredMatrix_zero H z hh] at he
  simpa using he

theorem conditional_signed_specht_many (μ : YoungDiagram)
    (e : Cell μ ≃ FreeSlot H 0) (a : Tail μ ≃ Fin k) (z : ℝ)
    (j : Fin b) (hj : 0 < bits j) (hh : h+k < Fintype.card (GridOutside bits j)) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g*realSign g:ℂ))) ≤ 0 :=
  conditional_signed_specht_one_le_zero H μ e a z (fun l hl x y =>
    signedPlacementEntry_zero_many H z j hj (by omega) x y)

theorem conditional_signed_specht_few (μ : YoungDiagram)
    (e : Cell μ ≃ FreeSlot H 0) (a : Tail μ ≃ Fin k)
    (j : Fin b) (hh : h+k+Fintype.card (GridOutside bits j) < gridSize bits) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H 0 g*realSign g:ℂ))) ≤ 0 :=
  conditional_signed_specht_one_le_zero H μ e a 0 (fun l hl x y =>
    signedPlacementEntry_zero_few H j (by omega) x y)

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter Topology

namespace BinaryCoordinateSweeps
open Young Irrep

variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

def signedCenteredHS (k : ℕ) (z : ℝ) : ℝ := ∑x : Placement H k 0, ∑y : Placement H k 0,
  ‖centeredMatrix (gridSize bits) (fun a => (conditionalGroupLaw H z a*realSign a:ℂ)) y x‖^2

lemma continuousAt_signedCenteredHS (k : ℕ) : ContinuousAt (signedCenteredHS H k) 0 := by
  unfold signedCenteredHS
  apply tendsto_finsetSum
  intro x _
  apply tendsto_finsetSum
  intro y _
  apply ContinuousAt.pow
  apply ContinuousAt.norm
  simp only [centeredMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply tendsto_finsetSum
  intro A _
  apply ContinuousAt.mul continuousAt_const
  apply tendsto_finsetSum
  intro g _
  have hc := Complex.continuous_ofReal.continuousAt.comp (continuousAt_conditionalGroupLaw H g)
  exact (hc.mul continuousAt_const).mul continuousAt_const

lemma signedCenteredHS_zero (k : ℕ) (z : ℝ)
    (hh : ∀ l ≤ k, ∀x : Placement H l 0, ∀y : Placement H l (Fin.last b),
      signedPlacementEntry H z x y=0) : signedCenteredHS H k z=0 := by
  unfold signedCenteredHS
  rw [signed_centeredMatrix_zero H z hh]
  simp

lemma conditional_signed_specht_hs {k : ℕ} (μ : YoungDiagram)
    (e : Cell μ ≃ FreeSlot H 0) (a : Tail μ ≃ Fin k) (z : ℝ) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g*realSign g:ℂ))) ≤ signedCenteredHS H k z := by
  rw [groupAverage_comp_slots]
  have hs : (gridSize bits:ℝ)≠0 := by exact_mod_cast (gridSize_pos bits).ne'
  have he := specht_moment_one_le_centered_matrix μ (gridSize bits) hs
    (fun g => (conditionalGroupLaw H z (e.permCongr g)*realSign (e.permCongr g):ℂ))
  have hr := centeredMatrix_hs_reindex a e (gridSize bits)
    (fun g => (conditionalGroupLaw H z (e.permCongr g)*realSign (e.permCongr g):ℂ))
  simp only [Equiv.apply_symm_apply] at hr
  rwa [←hr] at he

end BinaryCoordinateSweeps

end

end OAI
