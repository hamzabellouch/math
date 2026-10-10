import Mathlib
import OAI.Analysis.BrownMeasure.Modulus
import OAI.Analysis.BrownMeasure.Spectrum
import OAI.Analysis.FiniteFactor.CrossedProduct.Trace

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology
namespace FiniteFactor

def sourcePolarUnitary (θ : SourceCoordinate → ℝ) (n : ℤ) : unitary ProductOp :=
  ⟨sourceTransport θ 0 n,by
    constructor <;> simp only [sourceTransport_star,neg_zero,sourceTransport_mul,
      zero_add,neg_add_cancel,add_neg_cancel,sourceTransport_zero]⟩

def sourcePolarAutomorphism (θ : SourceCoordinate → ℝ) (n : ℤ) : ProductOp≃⋆ₐ[ℂ]ProductOp :=
  Unitary.conjStarAlgAut ℂ ProductOp (sourcePolarUnitary θ n)

lemma sourcePolarAutomorphism_apply (θ : SourceCoordinate → ℝ) (n : ℤ) (A : ProductOp) :
    sourcePolarAutomorphism θ n A=sourceTransport θ 0 n*A*sourceTransport θ 0 (-n) := by
  unfold sourcePolarAutomorphism
  rw [Unitary.conjStarAlgAut_apply]
  change sourceTransport θ 0 n*A*star (sourceTransport θ 0 n)=_
  rw [sourceTransport_star,neg_zero]

lemma sourcePolarAutomorphism_zero (θ : SourceCoordinate → ℝ) (A : ProductOp) :
    sourcePolarAutomorphism θ 0 A=A := by
  simp [sourcePolarAutomorphism_apply,sourceTransport_zero]

lemma sourcePolarAutomorphism_add (θ : SourceCoordinate → ℝ) (n m : ℤ) (A : ProductOp) :
    sourcePolarAutomorphism θ (n+m) A=sourcePolarAutomorphism θ n (sourcePolarAutomorphism θ m A) := by
  simp only [sourcePolarAutomorphism_apply]
  rw [show sourceTransport θ 0 (n+m)=sourceTransport θ 0 n*sourceTransport θ 0 m by
    rw [sourceTransport_mul,zero_add]]
  rw [show sourceTransport θ 0 (-(n+m))=sourceTransport θ 0 (-m)*sourceTransport θ 0 (-n) by
    rw [sourceTransport_mul,zero_add]; congr 1; omega]
  noncomm_ring

lemma sourcePolarAutomorphism_one (θ : SourceCoordinate → ℝ) (A : ProductOp) :
    sourcePolarAutomorphism θ 1 A=sourceShift SourceCoordinate*A*star (sourceShift SourceCoordinate) := by
  rw [sourcePolarAutomorphism_apply,sourceShift_eq_transport θ,sourceTransport_star,neg_zero]

lemma sourcePolarAutomorphism_family (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n m : ℤ) :
    sourcePolarAutomorphism θ n (sourcePolarFamily θ hθ m)=sourcePolarFamily θ hθ (n+m) := by
  rw [← sourceTransport_conjugate_pi θ hθ m,← sourceTransport_conjugate_pi θ hθ (n+m)]
  simpa only [sourcePolarAutomorphism_apply] using (sourcePolarAutomorphism_add θ n m (sourcePi θ (sourceWeightBase θ hθ))).symm

lemma sourcePolarTransport_mem (θ : SourceCoordinate → ℝ) (n : ℤ) :
    sourceTransport θ 0 n∈sourceAlgebra θ := by
  induction n using Int.induction_on with
  | zero => rw [sourceTransport_zero]; exact one_mem _
  | @succ n hn =>
    rw [show sourceTransport θ 0 (n+1)=sourceTransport θ 0 n*sourceTransport θ 0 1 by
      rw [sourceTransport_mul,zero_add]]
    exact mul_mem hn (by rw [← sourceShift_eq_transport θ]; exact sourceShift_mem θ)
  | @pred n hn =>
    rw [show sourceTransport θ 0 (-(n:ℤ)-1)=sourceTransport θ 0 (-(n:ℤ))*sourceTransport θ 0 (-1) by
      rw [sourceTransport_mul,zero_add]; congr 1]
    apply mul_mem hn
    have he : sourceTransport θ 0 (-1)=star (sourceShift SourceCoordinate) := by
      rw [sourceShift_eq_transport θ,sourceTransport_star,neg_zero]
    rw [he]
    exact star_mem (sourceShift_mem θ)

lemma sourcePolarAutomorphism_trace (θ : SourceCoordinate → ℝ) (n : ℤ) {A : ProductOp}
    (hA : A∈sourceAlgebra θ) :
    sourceVacuumFunctional (sourcePolarAutomorphism θ n A)=sourceVacuumFunctional A := by
  rw [sourcePolarAutomorphism_apply,
    sourceVacuumFunctional_tracial θ (mul_mem (sourcePolarTransport_mem θ n) hA)
      (sourcePolarTransport_mem θ (-n)),← mul_assoc,sourceTransport_mul]
  simp only [zero_add,neg_add_cancel,sourceTransport_zero,one_mul]

lemma sourceWeight_injective (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    Function.Injective (sourcePi θ (sourceWeightBase θ hθ)) := by
  intro u v he
  apply sourceOperator_injective θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
  change sourceShift SourceCoordinate (sourcePi θ (sourceWeightBase θ hθ) u)=
    sourceShift SourceCoordinate (sourcePi θ (sourceWeightBase θ hθ) v)
  rw [he]

lemma sourceOperator_spectrum (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    spectrum ℂ (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg)={0} :=
  spectrum_eq_zero_of_root_norm_tendsto _ (staged_sourceOperator_properties θ hθ).2.2.2
end FiniteFactor
end

end OAI
