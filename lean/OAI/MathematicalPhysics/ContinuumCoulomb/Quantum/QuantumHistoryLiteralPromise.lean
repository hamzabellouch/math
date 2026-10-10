import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialSourcePromise
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistorySourcePromise
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryRoutedEnergy

namespace OAI

/-! One polynomial promise exponent for the literal circuit-to-source
program, with the original verifier's empty circuits prepared explicitly. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistorySourceProgram
open QuantumHistorySpatial QuantumHistoryPreparedProgram QuantumPaddedLabelProgram
open QuantumAlgebraicHistory QuantumOrderedSourceIndex QuantumCoefficientPrograms

theorem circuit_polynomialPromise : ∃ k : ℕ, 0 < k ∧
    ∀ (c : QMACircuit) (_hc : c.WellFormed), (value c).PolynomialPromise k := by
  obtain ⟨a,ha⟩ := source_data_power
  refine ⟨2*a+6,by omega,fun c hc => ?_⟩
  let d := qmaNonemptyCircuit c
  let hd := qmaNonemptyCircuit_wellFormed c hc
  let ht := qmaNonemptyCircuit_sparse_pos c
  let he := qmaNonemptyCircuit_nearest c
  let I := QuantumHistorySpatial.input d hd ht he (precision c)
  let n := qubitCount (qmaPreparedCircuit c)
  have hn : 0 < n := qubitCount_positive _
  obtain ⟨L,hL,hC,hx,hy,hw⟩ := ha d hd ht he
  have lift (m : ℕ) (hm : m ≤ (n+2)^a) : (m:ℝ) ≤ (n+1:ℝ)^(2*a+6) := by
    have hb : m ≤ (n+1)^(2*a+6) := hm.trans
      ((power_base_change hn).trans (pow_le_pow_right₀ (by omega : 1 ≤ n+1) (by omega)))
    exact_mod_cast hb
  have hsize : n ≤ I.model.n := by
    have h := model_vertices_ge d hd ht he (precision c)
    rw [QuantumPaddedLabelProgram.historyQubits_eq] at h
    have hn' : n ≤ 4*(qubitCount (qmaSparseCircuit d)+3717*termCount (qmaSparseCircuit d)) := by
      change n ≤ 4*(n+_)
      omega
    exact hn'.trans h
  rw [value_actual c hc]
  apply QuantumFinalRoutingProgram.spatial_polynomialPromise I finalDensity_pos
    (N := (precision c:ℚ)) (T := precision c) (n := n)
    (by exact_mod_cast precision_pos c) (model_vertices_pos d hd ht he (precision c)) hsize
    hL (by simp only [Rat.cast_natCast,abs_of_nonneg (Nat.cast_nonneg _ : (0:ℝ) ≤ precision c)]; exact le_rfl)
    hC _ _ (xz_threshold_lt (qmaPreparedCircuit c)) (lift _ hx) (lift _ hy)
  · rw [route_rounds_eq]
    exact lift _ hw
  · exact final_threshold_gap_bound (qmaPreparedCircuit c) hn (time_le_qubitCount _) (by omega)

end ContinuumCoulomb.QuantumHistorySourceProgram

end

end OAI
