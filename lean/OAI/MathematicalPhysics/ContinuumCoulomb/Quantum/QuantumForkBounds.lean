import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkSpectrum
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingGraph

namespace OAI

/-! Polynomial coefficient and operator bounds for parallel degree reduction. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

def qmaForkOffset (J K : ℝ) : ℝ := 3/4+3*J^2+3*K^2

theorem qmaForkCorrection_exchange {n : ℕ} (site : Fin 3 → Fin n) (J K : ℝ) :
    qmaForkCorrection site J K =
      qmaExchangeMatrix (fun _ : Fin 1 => site 1)
        (fun _ : Fin 1 => site 2) (fun _ => 2*J*K) (qmaForkOffset J K) := by
  simp [qmaForkCorrection,qmaExchangeMatrix,qmaForkOffset,add_comm]

theorem qmaForkCorrection_lift_norm {n r : ℕ} (site : Fin 3 → Fin n)
    (hsite : Function.Injective site) (J K : ℝ) :
    ‖spinMatrixOperator (qmaForkCorrection site J K ⊗ₖ
      (1 : Matrix (MediatorBasis r) (MediatorBasis r) ℂ))‖ ≤ 12*(1+|J|+|K|)^2 := by
  have hneq (_a : Fin 1) : site 1 ≠ site 2 :=
    fun h => (by decide : (1 : Fin 3) ≠ 2) (hsite h)
  rw [qmaForkCorrection_exchange]
  apply (qmaExchangeMatrix_lift_norm _ _ hneq _ _).trans
  have hoff : 0 ≤ qmaForkOffset J K := by unfold qmaForkOffset; positivity
  rw [abs_of_nonneg hoff]
  simp [qmaForkOffset,abs_mul]
  nlinarith [sq_abs J,sq_abs K,abs_nonneg J,abs_nonneg K,mul_nonneg (abs_nonneg J) (abs_nonneg K)]

theorem qmaForkAmplitude_norm (R J K : ℝ) (hR : 0 ≤ R) :
    3*(∑ a, |qmaForkAmplitude R J K a|) = 3*R*(1+2*|J|+2*|K|) := by
  simp [qmaForkAmplitude,Fin.sum_univ_succ,abs_mul,abs_of_nonneg hR]
  ring

end ContinuumCoulomb

end

end OAI
