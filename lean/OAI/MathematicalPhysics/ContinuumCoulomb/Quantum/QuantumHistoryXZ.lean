import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryThreeLocalEnergy
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedXZEnergy

namespace OAI

/-! The literal X/Z family attached to the actual ordered verifier history,
including the scalar-sampling error and polynomial counts. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open scoped Classical

abbrev XZTerm (c : QMACircuit) (hT : 0 < c.gates.length) :=
  QuantumOrderedXZ.OutputTerm (OrderedPauliTerm c hT)

abbrev XZQubit (c : QMACircuit) (hT : 0 < c.gates.length) :=
  QuantumOrderedXZ.OutputQubit (qmaOrderedHistoryModel c hT).Q (OrderedPauliTerm c hT)

def xzWord (c : QMACircuit) (hT : 0 < c.gates.length) :
    XZTerm c hT → XZQubit c hT → Fin 4 :=
  QuantumOrderedXZ.word (historySites c hT) (orderedWord c hT)

def xzSites (c : QMACircuit) (hT : 0 < c.gates.length) :
    XZTerm c hT → List (XZQubit c hT) :=
  QuantumOrderedXZ.sites (historySites c hT) (orderedWord c hT)

def xzCoefficient (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) : XZTerm c hT → ℚ :=
  QuantumOrderedXZ.coefficient (sampledOrderedWeight (samplePrecision c N) c hT) N

def xzEnergy (c : QMACircuit) (hT : 0 < c.gates.length) (N : ℕ) : ℝ :=
  QuantumOrderedXZ.energy (historySites c hT) (orderedWord c hT)
    (sampledOrderedWeight (samplePrecision c N) c hT) N

theorem xz_sites_nodup (c : QMACircuit) (hT : 0 < c.gates.length) (p : XZTerm c hT) :
    (xzSites c hT p).Nodup :=
  QuantumOrderedXZ.sites_nodup _ _ (historySites_length c hT) (historySites_nodup c hT) p

theorem xz_sites_length (c : QMACircuit) (hT : 0 < c.gates.length) (p : XZTerm c hT) :
    (xzSites c hT p).length ≤ 2 :=
  QuantumOrderedXZ.sites_length _ _ (historySites_length c hT) p

theorem xz_sites_cover (c : QMACircuit) (hT : 0 < c.gates.length) (p : XZTerm c hT) :
    qmaPauliSupport (xzWord c hT p) ⊆ (xzSites c hT p).toFinset := by
  intro i hi
  have h := QuantumOrderedXZ.sites_cover (historySites c hT) (orderedWord c hT) p hi
  have hm : i ∈ xzSites c hT p := by
    simpa only [xzSites,List.mem_toFinset] using h
  exact List.mem_toFinset.mpr hm

theorem xz_noY (c : QMACircuit) (hT : 0 < c.gates.length) (p : XZTerm c hT)
    (i : XZQubit c hT) : xzWord c hT p i ≠ 2 :=
  QuantumOrderedXZ.noY _ _ (historySites_length c hT) (historySites_nodup c hT)
    (historySites_cover c hT) (orderedWord_even c hT) p i

theorem xz_support (c : QMACircuit) (hT : 0 < c.gates.length) (p : XZTerm c hT) :
    (qmaPauliSupport (xzWord c hT p)).card ≤ 2 :=
  QuantumOrderedXZ.support _ _ (historySites_length c hT) p

theorem xz_sampled_error (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) (hN : 0 < N) : |xzEnergy c hT N-sampledHistoryEnergy c hT N| ≤ 5/(N:ℝ) := by
  unfold xzEnergy sampledHistoryEnergy
  exact QuantumOrderedXZ.accuracy _ _ _ (historySites_length c hT)
    (historySites_nodup c hT) (historySites_cover c hT) (orderedWord_even c hT) N (by omega)

theorem xz_accuracy (c : QMACircuit) (hT : 0 < c.gates.length)
    (N : ℕ) (hN : 0 < N) :
    |xzEnergy c hT N-(qmaOrderedHistoryModel c hT).energy| ≤ 6/(N:ℝ) := by
  exact (abs_sub_le (xzEnergy c hT N) (sampledHistoryEnergy c hT N)
    (qmaOrderedHistoryModel c hT).energy).trans
      ((add_le_add (xz_sampled_error c hT N hN)
        (sampledHistory_error c hT N hN)).trans_eq (by ring))

theorem xz_term_count (c : QMACircuit) (hT : 0 < c.gates.length) :
    Fintype.card (XZTerm c hT) ≤ 3136*4096*(4*c.gates.length+2*c.work+9) := by
  rw [QuantumOrderedXZ.term_count]
  exact (Nat.mul_le_mul_left 3136 (orderedWord_count c hT)).trans_eq (by ring)

theorem xz_qubit_count (c : QMACircuit) (hT : 0 < c.gates.length) :
    Fintype.card (XZQubit c hT) ≤ 3*c.gates.length+2*c.work+8+
      581*4096*(4*c.gates.length+2*c.work+9) := by
  rw [QuantumOrderedXZ.qubit_count]
  have hq : Fintype.card (qmaOrderedHistoryModel c hT).Q =
      3*c.gates.length+2*c.work+8 := (qmaOrderedHistoryModel_size c hT).1
  rw [hq]
  exact Nat.add_le_add_left
    ((Nat.mul_le_mul_left 581 (orderedWord_count c hT)).trans_eq (by ring)) _

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
