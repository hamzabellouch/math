import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumNearestGate

namespace OAI

/-! Exact nearest-neighbor compilation with an explicit polynomial size bound. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

theorem qmaNearestList_matrix (work : ℕ) (gs : List QMAGate) :
    qmaGateProduct work (gs.flatMap (qmaNearestGate work)) = qmaGateProduct work gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change qmaGateProduct work (qmaNearestGate work g ++ gs.flatMap (qmaNearestGate work)) = _
    rw [qmaGateProduct_append,ih,qmaNearestGate_matrix]
    change _ = qmaGateProduct work ([g]++gs)
    rw [qmaGateProduct_append,qmaGateProduct_singleton]

theorem qmaNearestList_length (work : ℕ) (gs : List QMAGate) :
    (gs.flatMap (qmaNearestGate work)).length ≤ (6*work+7)*gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    have hg := qmaNearestGate_length work g
    nlinarith

abbrev qmaNearestCircuit (c : QMACircuit) : QMACircuit :=
  ⟨c.work,c.witness,c.gates.flatMap (qmaNearestGate c.work)⟩

theorem qmaNearestCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) :
    (qmaNearestCircuit c).WellFormed := by
  refine ⟨hc.1,?_⟩
  intro g hg
  obtain ⟨k,hk,hg⟩ := List.mem_flatMap.mp hg
  exact (qmaNearestGate_valid c.work k (hc.2 k hk) g hg).1

theorem qmaNearestCircuit_adjacent (c : QMACircuit) (hc : c.WellFormed) :
    ∀ g ∈ (qmaNearestCircuit c).gates, g.Adjacent := by
  intro g hg
  obtain ⟨k,hk,hg⟩ := List.mem_flatMap.mp hg
  exact (qmaNearestGate_valid c.work k (hc.2 k hk) g hg).2

theorem qmaNearestCircuit_acceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance (qmaNearestCircuit c) (qmaNearestCircuit_wellFormed c hc) psi =
      qmaAcceptance c hc psi := by
  have hm : qmaCircuitMatrix (qmaNearestCircuit c) = qmaCircuitMatrix c :=
    qmaNearestList_matrix c.work c.gates
  unfold qmaAcceptance
  rw [hm]
  rfl

theorem qmaNearestCircuit_size (c : QMACircuit) :
    (qmaNearestCircuit c).work+(qmaNearestCircuit c).gates.length ≤
      c.work+(6*c.work+7)*c.gates.length := by
  exact Nat.add_le_add_left (qmaNearestList_length c.work c.gates) c.work

end ContinuumCoulomb

end

end OAI
