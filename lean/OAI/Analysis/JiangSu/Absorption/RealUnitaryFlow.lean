import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.PointwiseMatching

namespace OAI

section

noncomputable section
namespace JiangSuConstruction
open Complex NormedSpace selfAdjoint Unitary
open scoped CStarAlgebra ComplexOrder

variable {A : Type*} [CStarAlgebra A]
local instance flowRationalAlgebra : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
local instance flowRationalTower : IsScalarTower ℚ ℂ A := IsScalarTower.restrictScalars ℚ ℂ A

def realUnitaryFlow (u : unitary A) (r : ℝ) : unitary A :=
  expUnitary (r • argSelfAdjoint u)

lemma realUnitaryFlow_continuous (u : unitary A) : Continuous (realUnitaryFlow u) := by
  unfold realUnitaryFlow
  fun_prop

@[simp] lemma realUnitaryFlow_zero (u : unitary A) : realUnitaryFlow u 0=1 := by
  simp [realUnitaryFlow]

lemma realUnitaryFlow_add (u : unitary A) (r s : ℝ) :
    realUnitaryFlow u (r+s)=realUnitaryFlow u r*realUnitaryFlow u s := by
  apply Subtype.ext
  change exp (I • ((r+s) • (argSelfAdjoint u : A)))=
    exp (I • (r • (argSelfAdjoint u : A)))*exp (I • (s • (argSelfAdjoint u : A)))
  rw [add_smul,smul_add]
  apply exp_add_of_commute
  exact ((((Commute.refl (argSelfAdjoint u : A)).smul_left r).smul_right s).smul_left I).smul_right I

@[simp] lemma realUnitaryFlow_neg (u : unitary A) (r : ℝ) :
    realUnitaryFlow u (-r)=(realUnitaryFlow u r)⁻¹ := by
  have h : realUnitaryFlow u r*realUnitaryFlow u (-r)=1 := by
    rw [←realUnitaryFlow_add,add_neg_cancel,realUnitaryFlow_zero]
  exact eq_inv_of_mul_eq_one_right h

lemma realUnitaryFlow_one (u : unitary A) (hf : (spectrum ℂ (u:A)).Finite) :
    realUnitaryFlow u 1=u := by
  simpa [realUnitaryFlow] using finite_spectrum_unitary_exp u hf

lemma realUnitaryFlow_commute (u : unitary A) {b : A} (h : Commute (u:A) b) (r : ℝ) :
    Commute (realUnitaryFlow u r : A) b := by
  change Commute (exp (I • (r • (argSelfAdjoint u : A)))) b
  exact (((unitary_argument_commute u h).smul_left r).smul_left I).exp_left

lemma realUnitaryFlow_commute_flow (u v : unitary A) (h : Commute u v) (r s : ℝ) :
    Commute (realUnitaryFlow u r) (realUnitaryFlow v s) := by
  have h' : Commute (u:A) (v:A) := congrArg Subtype.val h.eq
  have h₁ := (realUnitaryFlow_commute v h'.symm s).symm
  have h₂ := realUnitaryFlow_commute u h₁ r
  exact Subtype.ext h₂.eq

lemma realUnitaryFlow_mem (u : unitary A) (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (h : (u:A)∈S) (r : ℝ) :
    (realUnitaryFlow u r : A)∈S := by
  change exp (I • (r • (argSelfAdjoint u : A)))∈S
  apply exp_mem (R := ℂ) (s := S) (inferInstance : IsClosed (S : Set A))
  apply S.smul_mem
  change (r:ℂ) • (argSelfAdjoint u : A)∈S
  apply S.smul_mem
  rw [argSelfAdjoint_coe]
  exact cfc_mem (𝕜' := ℂ) _ h

lemma realUnitaryFlow_period_two (u : unitary A) (hf : (spectrum ℂ (u:A)).Finite)
    (hu : u*u=1) (r : ℝ) : realUnitaryFlow u (r+2)=realUnitaryFlow u r := by
  rw [realUnitaryFlow_add]
  have h : realUnitaryFlow u 2=1 := by
    rw [show (2:ℝ)=1+1 by norm_num,realUnitaryFlow_add,realUnitaryFlow_one u hf,hu]
  rw [h,mul_one]

end JiangSuConstruction

end
end

end OAI
