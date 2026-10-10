import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedHistory
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedTableProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryXZBounds

namespace OAI

/-! The literal padded history table has the same polynomial scalar budget
as the supported expansion, and its rational samples approximate the actual
full-space history energy. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedHistory
open QuantumAlgebraicScalar QuantumFixedPauli QuantumAlgebraicHistory
open scoped BigOperators Classical

section ScalarTable

local instance finDecision (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

private theorem padded_height (n m : ℕ)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) Scalar)
    (w : Fin (n+m) → Fin 4) (C : ℚ) (hC : 0 ≤ C)
    (hA : ∀ s t, height (A s t) ≤ C) :
    realHeight (QuantumPaddedTable.coefficient n m (matrixData A) w) ≤ 2^n*C := by
  let v := QuantumPaddedPauli.restrictWord n m w
  have hE : (fun s t : Fin n → Fin 2 => entry (matrixData A) s t) = A := by
    funext s t
    exact entry_matrixData A s t
  have hV : realHeight (realCoefficient A v) ≤ (2:ℚ)^n*C := by
    simpa only [Fintype.card_fin] using realHeight_coefficient A v C hA
  unfold QuantumPaddedTable.coefficient
  change realHeight (if Even (qmaPauliYCount v) then
    realMul (realRat (((4:ℚ)^m)⁻¹))
      (realCoefficient (fun s t => entry (matrixData A) s t) v) else realRat 0) ≤ _
  rw [hE]
  split_ifs
  · have hr : |((4:ℚ)^m)⁻¹| ≤ 1 := by
      rw [abs_of_pos (inv_pos.mpr (pow_pos (by norm_num) _))]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    calc
      _ ≤ realHeight (realRat (((4:ℚ)^m)⁻¹))*realHeight (realCoefficient A v) :=
        realHeight_mul _ _
      _ ≤ 1*realHeight (realCoefficient A v) := by
        rw [realHeight_rat]
        exact mul_le_mul_of_nonneg_right hr (realHeight_nonnegative _)
      _ ≤ (2:ℚ)^n*C := by simpa only [one_mul] using hV
  · simpa only [realHeight_rat,abs_zero] using mul_nonneg (pow_nonneg (by norm_num) n) hC

def scalar (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) : RealScalar :=
  QuantumPaddedTable.coefficient (QuantumOrderedSupport.sites c hT p.1).length
    (6-(QuantumOrderedSupport.sites c hT p.1).length)
    (matrixData (orderedTable c hT p.1))
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2)

theorem scalar_value (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    realValue (scalar c hT p) = coefficient c hT p := by
  unfold scalar coefficient tableMatrix
  exact QuantumPaddedTable.coefficient_value _ _ (orderedTable c hT p.1) _

theorem scalar_height (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    realHeight (scalar c hT p) ≤ (coefficientBudget c:ℚ) := by
  have h := padded_height _ _ (orderedTable c hT p.1)
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2)
    (2*historyHeight c) (mul_nonneg (by norm_num) (historyHeight_nonnegative c))
    (fun s t => height_orderedCore c hT p.1 _ _)
  have hp : (2:ℚ)^(QuantumOrderedSupport.sites c hT p.1).length ≤ 64 := by
    exact (pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2)
      (QuantumOrderedSupport.sites_length c hT p.1)).trans_eq (by norm_num)
  change realHeight (scalar c hT p) ≤ _ at h
  calc
    _ ≤ (2:ℚ)^(QuantumOrderedSupport.sites c hT p.1).length*(2*historyHeight c) := h
    _ ≤ 64*(2*historyHeight c) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg (by norm_num) (historyHeight_nonnegative c))
    _ = (coefficientBudget c:ℚ) := by rw [coefficientBudget_cast]; ring

end ScalarTable

def sampledWeight (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) : ℚ :=
  sample k (scalar c hT p)

theorem sampledWeight_bound (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length)
    (p : Term c) : |sampledWeight k c hT p| ≤ (coefficientBudget c:ℚ) :=
  (sample_height_bound k (scalar c hT p)).trans (scalar_height c hT p)

theorem sampled_error (k : ℕ) (c : QMACircuit) (hT : 0 < c.gates.length) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily (word c hT)
        (fun p => (sampledWeight k c hT p:ℝ)))-(qmaOrderedHistoryModel c hT).energy| ≤
      (termBudget c:ℝ)*(coefficientBudget c:ℝ)*(2:ℝ)⁻¹^k := by
  change |MediatorGraph.normalizedBottom _ -
    MediatorGraph.normalizedBottom (∑ a, (qmaOrderedHistoryModel c hT).matrix a)| ≤ _
  rw [← family_sum]
  have hround := qmaPauliFamily_ground_error (word c hT)
    (fun p => (sampledWeight k c hT p:ℝ)) (coefficient c hT)
  have hterm (p : Term c) :
      |(sampledWeight k c hT p:ℝ)-coefficient c hT p| ≤
        (coefficientBudget c:ℝ)*(2:ℝ)⁻¹^k := by
    rw [← scalar_value]
    exact (sample_error_height k (scalar c hT p)).trans
      (mul_le_mul_of_nonneg_right (Rat.cast_le.mpr (scalar_height c hT p)) (by positivity))
  apply hround.trans
  calc
    _ ≤ ∑ _p : Term c, (coefficientBudget c:ℝ)*(2:ℝ)⁻¹^k :=
      Finset.sum_le_sum (fun p _ => hterm p)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,term_count,termBudget,
        Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      ring

theorem sampled_accuracy (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) (hN : 0 < N) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily (word c hT)
        (fun p => (sampledWeight (samplePrecision c N) c hT p:ℝ)))-
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
  have hk : (k:ℝ) = (M+1)*(B+1)*N := by
    simp only [k,samplePrecision,M,B,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ M*B*(2:ℝ)⁻¹^k := sampled_error k c hT
    _ = M*B/((2:ℝ)^k) := by rw [inv_pow]; rfl
    _ ≤ M*B/((k:ℝ)+1) := div_le_div_of_nonneg_left (mul_nonneg hM hB) hkp hpow
    _ ≤ 1/(N:ℝ) := by
      apply (div_le_div_iff₀ hkp hNR).mpr
      rw [hk]
      nlinarith

end ContinuumCoulomb.QuantumPaddedHistory

end

end OAI
