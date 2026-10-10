import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarOneAtom

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def oneConfigEquiv : Bool ≃ Config 1 where
  toFun b := fun _ => b
  invFun s := s 0
  left_inv _ := rfl
  right_inv s := funext (fun i => congrArg s (Subsingleton.elim 0 i))

@[simp] theorem oneConfigEquiv_apply (b : Bool) (i : Fin 1) : oneConfigEquiv b i=b := rfl

theorem card_edge_one : Fintype.card (Edge 1)=0 := by
  let : IsEmpty (Edge 1) := ⟨fun e => by
    have he : e.val.1=e.val.2 := Subsingleton.elim _ _
    exact (lt_irrefl _ (he ▸ e.property))⟩
  exact Fintype.card_of_isEmpty

section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affineLogPartition_oneConfig (L : E →L[ℝ] ℝ) (z : E) :
    affineLogPartition (fun _ : Config 1 => 0) (fun s => spin (s 0) • L) z =
      scalarSpinTerminal (L z) := by
  change _ = Real.log (2*Real.cosh (L z))
  rw [← affineLogPartition_bool L z]
  unfold affineLogPartition
  congr 1

theorem affineMoment_oneConfig (L : E →L[ℝ] ℝ) (z : E) :
    affineMoment (fun _ : Config 1 => 0) (fun s => spin (s 0) • L) (fun s => spin (s 0)) z =
      scalarMagnetization (L z) := by
  unfold affineMoment affineGibbs
  rw [← oneConfigEquiv.sum_comp (fun t : Config 1 => Real.exp (0+(spin (t 0) • L) z))]
  rw [← oneConfigEquiv.sum_comp (fun s : Config 1 =>
    Real.exp (0+(spin (s 0) • L) z) /
      (∑ t : Bool, Real.exp (0+(spin ((oneConfigEquiv t) 0) • L) z))*spin (s 0))]
  simp only [oneConfigEquiv_apply,Fintype.sum_bool,smul_apply,smul_eq_mul,
    spin,Bool.false_eq_true,ite_false,ite_true,zero_add,one_mul,neg_one_mul,mul_one,mul_neg_one]
  unfold scalarMagnetization
  rw [Real.sinh_eq,Real.cosh_eq]
  field_simp
  ring

end Generic

end SK.Analytic

end
end

end OAI
