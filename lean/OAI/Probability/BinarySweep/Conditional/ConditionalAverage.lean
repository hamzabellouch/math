import Mathlib
import OAI.Probability.BinarySweep.Representations.IsotypicMoment
import OAI.Probability.BinarySweep.Conditional.Placement

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Representation

variable {b h : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h) (z : ℝ)

def conditionalGroupLaw (a : Equiv.Perm (FreeSlot H 0)) : ℝ :=
  ∑ g : ConditionalChoices H, if remainingPerm H g.val g.property=a then
    conditionalChoiceWeight H z g else 0

lemma conditionalGroupLaw_nonneg {z : ℝ} (hz : 0 ≤ z) (hz1 : z<1)
    (a : Equiv.Perm (FreeSlot H 0)) : 0 ≤ conditionalGroupLaw H z a := by
  apply Finset.sum_nonneg
  intro g _
  split_ifs
  · exact conditionalChoiceWeight_nonneg H hz hz1 g
  · rfl

lemma conditionalGroupLaw_sum {z : ℝ} (hz : 0 ≤ z) (hz1 : z<1) :
    ∑ a, conditionalGroupLaw H z a = 1 := by
  simp only [conditionalGroupLaw]
  rw [Finset.sum_comm]
  simpa using conditionalChoiceWeight_sum H hz hz1

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
lemma groupAverage_conditional (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V) :
    groupAverage ρ (fun a => (conditionalGroupLaw H z a : ℂ)) =
      ∑ g : ConditionalChoices H, (conditionalChoiceWeight H z g : ℂ) •
        ρ (remainingPerm H g.val g.property) := by
  simp only [groupAverage,conditionalGroupLaw,Complex.ofReal_sum,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp only [apply_ite,Complex.ofReal_zero,ite_smul,zero_smul]
  simp

omit [FiniteDimensional ℂ V] in
lemma groupAverage_conditional_grid (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) V) :
    groupAverage ρ (fun a => (conditionalGroupLaw H z a : ℂ)) =
      (conditionalNormalizer H z : ℂ)⁻¹ • ∑ g : GridChoices bits,
        if hg : pathEvent H g then (gridWeight bits z g : ℂ) •
          ρ (remainingPerm H g hg) else 0 := by
  rw [groupAverage_conditional]
  have hs : ∀ g : ConditionalChoices H,
      (conditionalChoiceWeight H z g : ℂ) • ρ (remainingPerm H g.val g.property) =
      (conditionalNormalizer H z : ℂ)⁻¹ •
        ((gridWeight bits z g.val : ℂ) • ρ (remainingPerm H g.val g.property)) := by
    intro g
    rw [conditionalChoiceWeight, Complex.ofReal_div, div_eq_mul_inv, mul_comm, mul_smul]
  simp_rw [hs]
  rw [← Finset.smul_sum]
  congr 1
  let F : GridChoices bits → (V →ₗ[ℂ] V) := fun g =>
    if hg : pathEvent H g then (gridWeight bits z g : ℂ) • ρ (remainingPerm H g hg) else 0
  have hF : ∑ g : ConditionalChoices H, F g.val = ∑ g, F g := by
    rw [← Finset.sum_filter_of_ne (p := pathEvent H) (f := F) (by
      intro g _ hg
      by_contra hn
      simp [F,hn] at hg)]
    exact (Finset.sum_subtype _ (by simp) _).symm
  simpa only [F,dite_eq_left (Subtype.property _)] using hF

lemma conditionalOperator_groupAverage {D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D)) :
    (conditionalOperator H z ρ).toLinearMap =
      groupAverage ρ (fun a => (conditionalGroupLaw H z a : ℂ)) := by
  rw [groupAverage_conditional_grid]
  rfl

lemma conditionalMoment_evenMoment {D : ℕ}
    (ρ : Representation ℂ (Equiv.Perm (FreeSlot H 0)) (RepSpace D)) (q : ℕ) :
    traceMoment q (conditionalOperator H z ρ) =
      evenMoment q (groupAverage ρ (fun a => (conditionalGroupLaw H z a : ℂ))) := by
  rw [← conditionalOperator_groupAverage]
  simp only [traceMoment,evenMoment,ContinuousLinearMap.toLinearMap_pow,
    ContinuousLinearMap.toLinearMap_mul,ContinuousLinearMap.adjoint_toLinearMap]

end BinaryCoordinateSweeps

end

end OAI
