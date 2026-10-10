import Mathlib
import OAI.Probability.BinarySweep.Conditional.ConditionalAverage
import OAI.Probability.BinarySweep.MatrixBounds.CenteredMatrix
import OAI.Probability.BinarySweep.SparseBounds.SparseKernel
import OAI.Probability.BinarySweep.Trajectories.EndpointPlacement

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Young Sparse

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma conditionalGroupLaw_expectation {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (z : ℝ) (f : Equiv.Perm (FreeSlot H 0) → W) :
    (∑a, conditionalGroupLaw H z a • f a) =
      ∑g : ConditionalChoices H, conditionalChoiceWeight H z g • f (remainingPerm H g.val g.property) := by
  unfold conditionalGroupLaw
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [ite_smul,zero_smul]
  simp

lemma partialKernel_event (g : ConditionalChoices H) (A : Finset (Fin k))
    (x y : Placement H k 0) :
    subPlacement A (movePlacement (remainingPerm H g.val g.property) x)=subPlacement A y ↔
      ∀i∈A, gridSweep bits g.val (x i).val=((placementIdentification H k y i).val) := by
  constructor
  · intro he i hi
    have hh := congrArg (fun u => u ⟨i,hi⟩) he
    have he' : remainingPerm H g.val g.property (x i)=y i := hh
    have ht := congrArg (freeIdentification H) he'
    change (freeIdentification H) ((freeIdentification H).symm
      (remainingBijection H g.val g.property (x i)))=(freeIdentification H) (y i) at ht
    rw [Equiv.apply_symm_apply] at ht
    exact congrArg Subtype.val ht
  · intro he
    apply Function.Embedding.ext
    intro i
    change (freeIdentification H).symm (remainingBijection H g.val g.property (x i.val))=y i.val
    apply (freeIdentification H).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    exact he i.val i.property

lemma partialKernel_conditional (z : ℝ) (A : Finset (Fin k)) (x y : Placement H k 0) :
    (∑a : Equiv.Perm (FreeSlot H 0), (conditionalGroupLaw H z a:ℂ) * partialKernel A a y x)=
      (endpointProbability H z A (fun i => ((x i).val,(placementIdentification H k y i).val)):ℂ) := by
  have he := conditionalGroupLaw_expectation H z (fun a => partialKernel A a y x)
  simp only [Complex.real_smul] at he
  rw [he,endpointProbability_conditional]
  unfold conditionalEventWeight
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr
  · ext g; simp only [Finset.mem_univ]
  intro g _
  simp only [partialKernel,partialKernel_event H g A x y]
  split_ifs <;> simp

theorem centeredMatrix_conditional (z : ℝ) (x y : Placement H k 0) :
    centeredMatrix (gridSize bits) (fun a => (conditionalGroupLaw H z a:ℂ)) y x =
      (centeredEndpointKernel H z (fun i => ((x i).val,(placementIdentification H k y i).val)):ℂ) := by
  simp only [centeredMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  simp_rw [partialKernel_conditional H z]
  unfold centeredEndpointKernel alternatingSubsetSum
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv,Complex.ofReal_natCast,
    Complex.ofReal_sum,Complex.ofReal_neg,Complex.ofReal_one,Finset.card_univ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [div_eq_mul_inv,inv_pow]
  ring

end BinaryCoordinateSweeps

end

end OAI
