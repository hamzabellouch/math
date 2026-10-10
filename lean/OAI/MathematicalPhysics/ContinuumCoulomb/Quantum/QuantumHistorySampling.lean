import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryHeight
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSampling

namespace OAI

/-! One explicit unary precision controls the total error of all actual
ordered-history coefficients.  The precision is polynomial in the circuit
size and the requested inverse error. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped BigOperators Classical

def coefficientBudget (c : QMACircuit) : ℕ :=
  128*(14+288*((14*(c.work+1)+8)*c.gates.length))

def termBudget (c : QMACircuit) : ℕ := 4096*(4*c.gates.length+2*c.work+9)

def samplePrecision (c : QMACircuit) (N : ℕ) : ℕ :=
  (termBudget c+1)*(coefficientBudget c+1)*N

theorem coefficientBudget_cast (c : QMACircuit) :
    (coefficientBudget c:ℚ) = 128*historyHeight c := by
  simp only [coefficientBudget,historyHeight,Nat.cast_mul,Nat.cast_add,
    Nat.cast_one,Nat.cast_ofNat]

theorem orderedCoefficient_second_bound (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : OrderedPauliTerm c hT) :
    |((orderedRealCoefficient c hT p).2:ℝ)| ≤ coefficientBudget c := by
  have hfirst : |(orderedRealCoefficient c hT p).2| ≤
      realHeight (orderedRealCoefficient c hT p) :=
    le_add_of_nonneg_left (abs_nonneg _)
  have hsecond : realHeight (orderedRealCoefficient c hT p) ≤ (coefficientBudget c:ℚ) := by
    rw [coefficientBudget_cast]
    exact orderedCoefficient_height c hT p.val.1 p.val.2
  exact_mod_cast hfirst.trans hsecond

theorem sampledOrdered_accuracy (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom
      (qmaPauliFamily (orderedWord c hT)
        (fun p => (sampledOrderedWeight (samplePrecision c N) c hT p:ℝ))) -
          (qmaOrderedHistoryModel c hT).energy| ≤ 1/(N:ℝ) := by
  let k := samplePrecision c N
  let M := (termBudget c:ℝ)
  let B := (coefficientBudget c:ℝ)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hpow : (k:ℝ)+1 ≤ (2:ℝ)^k := by
    have hp : k+1 ≤ 2^k := Nat.succ_le_iff.mpr (Nat.lt_two_pow_self (n := k))
    exact_mod_cast hp
  have hkp : (0:ℝ) < (k:ℝ)+1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) (by norm_num)
  have hcard : (Fintype.card (OrderedPauliTerm c hT):ℝ) ≤ M := by
    change (Fintype.card (OrderedPauliTerm c hT):ℝ) ≤ (termBudget c:ℝ)
    unfold termBudget
    exact_mod_cast orderedWord_count c hT
  have hk : (k:ℝ) = (M+1)*(B+1)*N := by
    simp only [k,samplePrecision,M,B,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ ∑ p : OrderedPauliTerm c hT,
        |((orderedRealCoefficient c hT p).2:ℝ)| * (2:ℝ)⁻¹^k :=
      sampledOrdered_error k c hT
    _ ≤ ∑ _p : OrderedPauliTerm c hT, B*(2:ℝ)⁻¹^k := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right (orderedCoefficient_second_bound c hT p)
        (by positivity)
    _ = (Fintype.card (OrderedPauliTerm c hT):ℝ)*B*(2:ℝ)⁻¹^k := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring
    _ ≤ M*B*(2:ℝ)⁻¹^k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hB) (by positivity)
    _ = M*B/((2:ℝ)^k) := by rw [inv_pow]; rfl
    _ ≤ M*B/((k:ℝ)+1) := div_le_div_of_nonneg_left (mul_nonneg hM hB) hkp hpow
    _ ≤ 1/(N:ℝ) := by
      apply (div_le_div_iff₀ hkp hNR).mpr
      rw [hk]
      nlinarith

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
