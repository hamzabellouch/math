import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalError
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCircuitPauli

namespace OAI

/-! Exact low-block algebra for subdivision and three-body mediator gadgets. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaGadget_pair_square (A B : Matrix ι ι ℂ) (b : ℂ)
    (hA : A*A = 1) (hB : B*B = 1) (hAB : A*B = B*A) :
    (A+b • B)*(A+b • B) = (1+b^2) • (1 : Matrix ι ι ℂ)+(2*b) • (A*B) := by
  calc
    _ = A*A+b • (A*B)+b • (B*A)+(b*b) • (B*B) := by
      simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_add,smul_smul]
      abel
    _ = _ := by
      rw [hA,hB,←hAB]
      module

theorem qmaGadget_pair_sandwich (A B C : Matrix ι ι ℂ) (b : ℂ)
    (hA : A*A = 1) (hB : B*B = 1) (hAB : A*B = B*A)
    (hAC : A*C = C*A) (hBC : B*C = C*B) :
    (A+b • B)*C*(A+b • B) = (1+b^2) • C+(2*b) • (A*B*C) := by
  have hc : (A+b • B)*C = C*(A+b • B) := by
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,hAC,hBC]
  rw [hc,mul_assoc,qmaGadget_pair_square A B b hA hB hAB,mul_add,mul_smul_comm,
    mul_smul_comm,mul_one]
  have he : C*(A*B) = A*B*C := by
    rw [←mul_assoc,←hAC,mul_assoc,←hBC,←mul_assoc]
  rw [he]

theorem qmaGadget_penalty_product (C : Matrix ι ι ℂ) (a b : ℂ) (hC : C*C = 1) :
    (a • (1 : Matrix ι ι ℂ)+b • C)*(a • (1 : Matrix ι ι ℂ)-b • C) =
      (a^2-b^2) • (1 : Matrix ι ι ℂ) := by
  simp only [add_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,hC]
  module

def qmaGadgetPenaltyInverse (C : Matrix ι ι ℂ) (a b : ℂ) : Matrix ι ι ℂ :=
  (a^2-b^2)⁻¹ • (a • (1 : Matrix ι ι ℂ)-b • C)

theorem qmaGadgetPenaltyInverse_right (C : Matrix ι ι ℂ) (a b : ℂ)
    (hC : C*C = 1) (hab : a^2-b^2 ≠ 0) :
    (a • (1 : Matrix ι ι ℂ)+b • C)*qmaGadgetPenaltyInverse C a b = 1 := by
  rw [qmaGadgetPenaltyInverse,mul_smul_comm,qmaGadget_penalty_product C a b hC,
    smul_smul,inv_mul_cancel₀ hab,one_smul]

theorem qmaGadget_effective (A B C : Matrix ι ι ℂ) (a b c : ℂ)
    (hA : A*A = 1) (hB : B*B = 1) (hAB : A*B = B*A)
    (hAC : A*C = C*A) (hBC : B*C = C*B) :
    (A+c • B)*qmaGadgetPenaltyInverse C a b*(A+c • B) =
      (a^2-b^2)⁻¹ •
        (a • ((1+c^2) • (1 : Matrix ι ι ℂ)+(2*c) • (A*B))-
          b • ((1+c^2) • C+(2*c) • (A*B*C))) := by
  rw [qmaGadgetPenaltyInverse,mul_smul_comm,smul_mul_assoc,mul_sub,
    mul_smul_comm,mul_smul_comm,mul_one,sub_mul,smul_mul_assoc,smul_mul_assoc,
    qmaGadget_pair_square A B c hA hB hAB,qmaGadget_pair_sandwich A B C c hA hB hAB hAC hBC]

end ContinuumCoulomb

end

end OAI
