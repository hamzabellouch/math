import Mathlib
import OAI.Probability.BinarySweep.SparseBounds.SparseAmplitude
import OAI.Probability.BinarySweep.SparseBounds.ConditionalCentered
import OAI.Probability.BinarySweep.SparseBounds.CenteredReindex

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young Irrep

variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma groupAverage_comp_slots {X Y V : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (e : X ≃ Y) (ρ : Representation ℂ (Equiv.Perm X) V) (p : Equiv.Perm Y → ℂ) :
    groupAverage (ρ.comp e.symm.permCongrHom.toMonoidHom) p =
      groupAverage ρ (fun g => p (e.permCongr g)) := by
  unfold groupAverage
  rw [← Equiv.sum_comp e.permCongr]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  change ρ (e.permCongr.symm (e.permCongr g))=ρ g
  rw [Equiv.symm_apply_apply]

theorem conditional_specht_hs (μ : YoungDiagram) (e : Cell μ ≃ FreeSlot H 0)
    (a : Tail μ ≃ Fin k) (z : ℝ) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ))) ≤
      ∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
        (centeredEndpointKernel H z (fun i => ((x i).val,(y i).val)))^2 := by
  rw [groupAverage_comp_slots]
  have hs : (gridSize bits:ℝ)≠0 := by exact_mod_cast (gridSize_pos bits).ne'
  have he := specht_moment_one_le_centered_matrix μ (gridSize bits) hs
    (fun g => (conditionalGroupLaw H z (e.permCongr g):ℂ))
  have hr := centeredMatrix_hs_reindex a e (gridSize bits)
    (fun g => (conditionalGroupLaw H z (e.permCongr g):ℂ))
  simp only [Equiv.apply_symm_apply] at hr
  rw [← hr] at he
  refine he.trans_eq ?_
  change (∑x : Placement H k 0, ∑y : Placement H k 0,
    ‖centeredMatrix (gridSize bits) (fun g => (conditionalGroupLaw H z g:ℂ)) y x‖^2)=_
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [centeredMatrix_conditional H z,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact Equiv.sum_comp (placementIdentification H k) (fun y : Placement H k (Fin.last b) =>
    (centeredEndpointKernel H z (fun i => ((x i).val,(y i).val)))^2)

theorem conditional_specht_many_bound (μ : YoungDiagram) (e : Cell μ ≃ FreeSlot H 0)
    (a : Tail μ ≃ Fin k) (hd : ∀j, bits j≤2*r) {z : ℝ}
    (hz : 0≤z) (hzr : z≤linePerturbationRadius r) (hz1 : z<1)
    (hsmall : ((k+h:ℕ):ℝ) * (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j)) ≤ 1) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom)
      (fun g => (conditionalGroupLaw H z g:ℂ))) ≤
      ((2:ℝ)^k * Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
        ((2:ℝ)^k * (((k+h:ℕ):ℝ) *
          (∑j : Fin b, (1:ℝ)/Fintype.card (GridOutside bits j)))^((k+1)/2)) :=
  (conditional_specht_hs H μ e a z).trans
    (centeredEndpointKernel_hs_bound H hd hz hzr hz1 hsmall)

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical
open Filter Topology

namespace BinaryCoordinateSweeps
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma continuous_lineLaw (d : ℕ) (g : Equiv.Perm (Slot d)) :
    Continuous (fun z => lineLaw d z g) := by
  unfold lineLaw
  fun_prop

lemma continuous_gridWeight (g : GridChoices bits) : Continuous (fun z => gridWeight bits z g) := by
  unfold gridWeight
  exact continuous_finsetProd _ (fun j _ => continuous_finsetProd _ (fun y _ => continuous_lineLaw _ _))

lemma continuous_conditionalNormalizer : Continuous (conditionalNormalizer H) := by
  unfold conditionalNormalizer
  apply continuous_finsetSum
  intro g _
  split_ifs
  · exact continuous_gridWeight g
  · exact continuous_const

lemma continuousAt_conditionalChoiceWeight (g : ConditionalChoices H) :
    ContinuousAt (fun z => conditionalChoiceWeight H z g) 0 :=
  (continuous_gridWeight g.val).continuousAt.div (continuous_conditionalNormalizer H).continuousAt
    (conditionalNormalizer_pos H (le_refl 0) (by norm_num)).ne'

lemma continuousAt_conditionalGroupLaw (a : Equiv.Perm (FreeSlot H 0)) :
    ContinuousAt (fun z => conditionalGroupLaw H z a) 0 := by
  unfold conditionalGroupLaw
  apply tendsto_finsetSum
  intro g _
  split_ifs
  · exact continuousAt_conditionalChoiceWeight H g
  · exact continuousAt_const

lemma continuousAt_endpointProbability {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (e : I → GridSlot bits × GridSlot bits) :
    ContinuousAt (fun z => endpointProbability H z A e) 0 := by
  simp_rw [endpointProbability_conditional]
  unfold conditionalEventWeight
  apply tendsto_finsetSum
  intro g _
  split_ifs
  · exact continuousAt_conditionalChoiceWeight H g
  · exact continuousAt_const

lemma continuousAt_centeredEndpointKernel {I : Type*} [Fintype I] [DecidableEq I]
    (e : I → GridSlot bits × GridSlot bits) :
    ContinuousAt (fun z => centeredEndpointKernel H z e) 0 := by
  unfold centeredEndpointKernel alternatingSubsetSum
  apply ContinuousAt.mul continuousAt_const
  apply tendsto_finsetSum
  intro A _
  exact continuousAt_const.mul (continuousAt_endpointProbability H A e)

lemma continuousAt_centeredEndpointHS (k : ℕ) :
    ContinuousAt (fun z => ∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H z (fun i => ((x i).val,(y i).val)))^2) 0 := by
  apply tendsto_finsetSum
  intro x _
  apply tendsto_finsetSum
  intro y _
  exact (continuousAt_centeredEndpointKernel H _).pow 2

end BinaryCoordinateSweeps

end

end OAI
