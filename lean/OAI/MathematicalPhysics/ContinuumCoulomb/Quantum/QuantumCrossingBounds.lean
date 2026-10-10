import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingGraph

namespace OAI

/-! Polynomial coefficient and operator bounds for the crossing construction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaCrossingLeft : Fin 4 → Fin 4 := ![0,0,1,2]
def qmaCrossingRight : Fin 4 → Fin 4 := ![1,3,2,3]
def qmaCrossingWeight (J K : ℝ) : Fin 4 → ℝ := ![1/2,-K,-J,2*J*K]
def qmaCrossingOffset (J K : ℝ) : ℝ := 3/2+3*J^2+3*K^2

theorem qmaCrossingCorrection_exchange {n : ℕ} (site : Fin 4 → Fin n) (J K : ℝ) :
    qmaCrossingCorrection site J K =
      qmaExchangeMatrix (fun a => site (qmaCrossingLeft a))
        (fun a => site (qmaCrossingRight a)) (qmaCrossingWeight J K) (qmaCrossingOffset J K) := by
  simp [qmaCrossingCorrection,qmaExchangeMatrix,qmaCrossingLeft,qmaCrossingRight,
    qmaCrossingWeight,qmaCrossingOffset,Fin.sum_univ_succ]
  module

theorem qmaCrossingCorrection_lift_norm {n r : ℕ} (site : Fin 4 → Fin n)
    (hsite : Function.Injective site) (J K : ℝ) :
    ‖spinMatrixOperator (qmaCrossingCorrection site J K ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ 12*(1+|J|+|K|)^2 := by
  have hneq (a : Fin 4) : site (qmaCrossingLeft a) ≠ site (qmaCrossingRight a) := by
    intro h
    have hh := hsite h
    fin_cases a <;> norm_num [qmaCrossingLeft,qmaCrossingRight] at hh
  rw [qmaCrossingCorrection_exchange]
  apply (qmaExchangeMatrix_lift_norm _ _ hneq _ _).trans
  have hoff : 0 ≤ qmaCrossingOffset J K := by unfold qmaCrossingOffset; positivity
  rw [abs_of_nonneg hoff]
  simp [qmaCrossingWeight,qmaCrossingOffset,Fin.sum_univ_succ,abs_mul,abs_neg]
  nlinarith [sq_abs J,sq_abs K,abs_nonneg J,abs_nonneg K,mul_nonneg (abs_nonneg J) (abs_nonneg K)]

theorem qmaCrossingAmplitude_norm (R J K : ℝ) (hR : 0 ≤ R) :
    3*(∑ a, |qmaCrossingAmplitude R J K a|) = 6*R*(1+|J|+|K|) := by
  simp [qmaCrossingAmplitude,Fin.sum_univ_succ,abs_mul,abs_of_nonneg hR]
  ring

end ContinuumCoulomb

end

end OAI
