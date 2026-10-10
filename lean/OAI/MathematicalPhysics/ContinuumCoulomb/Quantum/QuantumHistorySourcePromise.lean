import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistorySourcePowers
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPreparedLattice

namespace OAI

/-! The specified verifier output satisfies the exact polynomial source
promise, with one exponent for all circuits, including empty-circuit padding. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySpatial
open QuantumOrderedSourceIndex QuantumAlgebraicHistory QuantumCoefficientPrograms

theorem source_polynomialPromise : ∃ k : ℕ, 0 < k ∧
    ∀ (c : QMACircuit) (hc : c.WellFormed)
      (hT : 0 < (qmaSparseCircuit c).gates.length)
      (hne : (qmaNearestCircuit c).gates ≠ []),
      (source c hc hT hne).binary.PolynomialPromise k := by
  obtain ⟨a,ha⟩ := source_data_power
  refine ⟨2*a+6,by omega,fun c hc hT hne => ?_⟩
  let n := qubitCount (qmaSparseCircuit c)
  have hn : 0 < n := qubitCount_positive _
  obtain ⟨L,hL,hC,hx,hy,hw⟩ := ha c hc hT hne
  have lift (m : ℕ) (hm : m ≤ (n+2)^a) : (m:ℝ) ≤ (n+1:ℝ)^(2*a+6) := by
    have hb : m ≤ (n+1)^(2*a+6) := hm.trans
      ((power_base_change hn).trans
        (pow_le_pow_right₀ (by omega : 1 ≤ n+1) (by omega)))
    exact_mod_cast hb
  have hsize : n ≤ (model c hc hT hne (latticePrecision c)).n := by
    have h := model_vertices_ge c hc hT hne (latticePrecision c)
    rw [QuantumPaddedLabelProgram.historyQubits_eq] at h
    dsimp only [n]
    omega
  unfold source
  apply (model c hc hT hne (latticePrecision c)).latticeSource_binary_promise
    finalDensity_pos (model_degree c hc hT hne (latticePrecision c))
    (latticePrecision c:ℚ) (model_vertices_pos c hc hT hne (latticePrecision c))
    (xzYesThreshold (qmaSparseCircuit c)) (xzNoThreshold (qmaSparseCircuit c))
    (xz_threshold_lt (qmaSparseCircuit c)) hsize
    (by exact_mod_cast Nat.zero_le (latticePrecision c)) hL
    (by simp only [Rat.cast_natCast,abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ) ≤ latticePrecision c)]; exact le_rfl) hC
    (lift _ hx) (lift _ hy)
  · rw [routeRounds_eq]
    exact lift _ hw
  · exact final_threshold_gap_bound (qmaSparseCircuit c) hn
      (time_le_qubitCount _) (by omega)

theorem preparedSource_polynomialPromise : ∃ k : ℕ, 0 < k ∧
    ∀ (c : QMACircuit) (hc : c.WellFormed),
      (preparedSource c hc).binary.PolynomialPromise k := by
  obtain ⟨k,hk,h⟩ := source_polynomialPromise
  exact ⟨k,hk,fun c hc => h (qmaNonemptyCircuit c) (qmaNonemptyCircuit_wellFormed c hc)
    (qmaNonemptyCircuit_sparse_pos c) (qmaNonemptyCircuit_nearest c)⟩

end ContinuumCoulomb.QuantumHistorySpatial

end

end OAI
