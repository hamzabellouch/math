import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedWeightBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelCompile

namespace OAI

/-! An integer polynomial bound for the complete six-stage ordered compiler,
including the private-pair subdivision before the physical four-spin step. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedXZ
open scoped Classical

def weightNat (R B : ℕ) : ℕ := R^3+R^2*B+R^2+R*(1+B^2)+1+B^2
def scaleNat (m B N : ℕ) : ℕ := 8*(4*(1+m*(1+B)^2))^4*N
def stepNat (m B N : ℕ) : ℕ := weightNat (scaleNat m B N) B
def pipelineNat (m B N : ℕ) : ℕ → ℕ
  | 0 => B
  | k+1 => stepNat (3136*m) (pipelineNat m B N k) N

theorem weightNat_cast (R B : ℕ) : (weightNat R B:ℚ)=weightEnvelope R B := by
  simp only [weightNat,weightEnvelope,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_one]

theorem scaleNat_cast (m B N : ℕ) : (scaleNat m B N:ℚ)=scaleEnvelope m B N := by
  simp only [scaleNat,scaleEnvelope,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
    Nat.cast_one,Nat.cast_ofNat]

theorem stepNat_cast (m B N : ℕ) : (stepNat m B N:ℚ)=stepEnvelope m B N := by
  simp only [stepNat,stepEnvelope,weightNat_cast,scaleNat_cast]

theorem pipelineNat_cast (m B N k : ℕ) : (pipelineNat m B N k:ℚ)=pipelineBound m B N k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pipelineNat,stepNat_cast,ih,pipelineBound]

theorem outputTerm_card {κ : Type} [Fintype κ] :
    Fintype.card (OutputTerm κ)=3136*Fintype.card κ := by
  simp only [OutputTerm,XZThreeTerm,TwoTerm,ThreeTerm,Fintype.card_prod,Fintype.card_fin]
  ring

theorem private_coefficient_bound {κ : Type} [Fintype κ] (J : κ → ℚ)
    {m B : ℕ} (hm : Fintype.card κ ≤ m) (hJ : ∀ e, |J e| ≤ (B:ℚ))
    (N : ℕ) (p : OutputTerm κ × Fin 4) :
    |QuantumOrderedPrivate.outputCoefficient (coefficient J N) N p| ≤
      (pipelineNat m B N 6:ℚ) := by
  have hB : (0:ℚ) ≤ B := Nat.cast_nonneg B
  have hc := pipeline_coefficient_bound J hB hm hJ N
  have hcount : Fintype.card (OutputTerm κ) ≤ 3136*m := by
    rw [outputTerm_card]
    exact Nat.mul_le_mul_left 3136 hm
  have h := subdivision_coefficient_bound (coefficient J N)
    (pipelineBound_nonneg m hB N 5) hcount hc N p
  change |QuantumOrderedSubdivision.outputCoefficient (coefficient J N) N p| ≤
    (stepNat (3136*m) (pipelineNat m B N 5) N:ℚ)
  rw [stepNat_cast,pipelineNat_cast]
  exact h

end ContinuumCoulomb.QuantumOrderedXZ

end

end OAI
