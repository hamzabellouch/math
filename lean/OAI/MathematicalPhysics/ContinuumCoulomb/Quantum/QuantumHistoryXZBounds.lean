import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryXZ
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedWeightBounds

namespace OAI

/-! Coefficient control for the actual sampled verifier history throughout
the five fixed gadget stages. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar
open scoped Classical

private theorem halfRoot_bounds (k : ℕ) :
    0 ≤ RationalSquareRoot.value (k,1/2) ∧ RationalSquareRoot.value (k,1/2) ≤ 1 := by
  have hv : RationalSquareRoot.value (k,(1/2:ℚ)) = DyadicRootProgram.value k 1 2 := by
    norm_num [RationalSquareRoot.value]
  rw [hv]
  constructor
  · unfold DyadicRootProgram.value
    positivity
  · have h := (DyadicRootProgram.value_error k 1 2 (by omega)).1
    have hs : Real.sqrt ((1:ℝ)/2) ≤ 1 := (Real.sqrt_le_iff).mpr (by norm_num)
    have ht : (DyadicRootProgram.value k 1 2:ℝ) ≤ 1 := by
      norm_num only [Nat.cast_one,Nat.cast_ofNat] at h
      linarith
    exact_mod_cast ht

theorem sample_height_bound (k : ℕ) (x : RealScalar) : |sample k x| ≤ realHeight x := by
  have h := halfRoot_bounds k
  calc
    _ ≤ |x.1|+|x.2*RationalSquareRoot.value (k,1/2)| := abs_add_le _ _
    _ = |x.1|+|x.2| * RationalSquareRoot.value (k,1/2) := by
      rw [abs_mul,abs_of_nonneg h.1]
    _ ≤ |x.1|+|x.2| * 1 := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left h.2 (abs_nonneg _))
    _ = realHeight x := by simp only [realHeight,mul_one]

theorem sampledOrdered_weight_bound (c : QMACircuit) (hT : 0 < c.gates.length)
    (k : ℕ) (p : OrderedPauliTerm c hT) :
    |sampledOrderedWeight k c hT p| ≤ (coefficientBudget c:ℚ) := by
  apply (sample_height_bound k (orderedRealCoefficient c hT p)).trans
  rw [coefficientBudget_cast]
  exact orderedCoefficient_height c hT p.val.1 p.val.2

def xzCoefficientBound (c : QMACircuit) (N : ℕ) : ℚ :=
  QuantumOrderedXZ.pipelineBound (termBudget c) (coefficientBudget c) N 5

theorem xzCoefficient_bound (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) (p : XZTerm c hT) : |xzCoefficient c hT N p| ≤ xzCoefficientBound c N := by
  apply QuantumOrderedXZ.pipeline_coefficient_bound
    (sampledOrderedWeight (samplePrecision c N) c hT)
    (show (0:ℚ) ≤ coefficientBudget c from Nat.cast_nonneg _)
    (show Fintype.card (OrderedPauliTerm c hT) ≤ termBudget c from orderedWord_count c hT)
    (sampledOrdered_weight_bound c hT (samplePrecision c N)) N p

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
