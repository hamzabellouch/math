import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZThird
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionEnvelope

namespace OAI

/-! Every explicit X/Z gadget word stays in its original support plus its mediator. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem qmaJoinedWord_envelope (w : ι → Fin 4) (e : κ) (a : Fin 4) {S : Finset ι}
    (h : qmaPauliSupport w ⊆ S) :
    qmaPauliSupport (Sum.elim w (qmaSinglePauliWord e a)) ⊆ qmaMediatorSupport S e := by
  rw [qmaPauliSupport_join]
  exact Finset.union_subset_union (Finset.map_subset_map.mpr h)
    (Finset.map_subset_map.mpr (qmaSinglePauliWord_support e a))

theorem qmaJoinedLeftWord_envelope (w : ι → Fin 4) (e : κ) {S : Finset ι}
    (h : qmaPauliSupport w ⊆ S) :
    qmaPauliSupport (Sum.elim w (fun _ : κ => 0)) ⊆ qmaMediatorSupport S e := by
  rw [qmaPauliSupport_join]
  apply Finset.union_subset_union (Finset.map_subset_map.mpr h)
  simp [qmaPauliSupport]

theorem qmaXZSubdivisionWord_envelope (a b : ι → Fin 4) (e : κ) {S : Finset ι}
    (ha : qmaPauliSupport a ⊆ S) (hb : qmaPauliSupport b ⊆ S) (k : Fin 4) :
    qmaPauliSupport (qmaXZSubdivisionWord a b e k) ⊆ qmaMediatorSupport S e := by
  fin_cases k
  · simp [qmaXZSubdivisionWord,qmaPauliSupport]
  · exact qmaJoinedWord_envelope (fun _ => 0) e 3 (by simp [qmaPauliSupport])
  · exact qmaJoinedWord_envelope a e 1 ha
  · exact qmaJoinedWord_envelope b e 1 hb

theorem qmaXZThirdWord_envelope (a b c v : ι → Fin 4) (e : κ) {S : Finset ι}
    (ha : qmaPauliSupport a ⊆ S) (hb : qmaPauliSupport b ⊆ S)
    (hc : qmaPauliSupport c ⊆ S) (hv : qmaPauliSupport v ⊆ S) (k : Fin 7) :
    qmaPauliSupport (qmaXZThirdWord a b c v e k) ⊆ qmaMediatorSupport S e := by
  fin_cases k
  · simp [qmaXZThirdWord,qmaPauliSupport]
  · exact qmaJoinedWord_envelope (fun _ => 0) e 3 (by simp [qmaPauliSupport])
  · exact qmaJoinedLeftWord_envelope v e hv
  · exact qmaJoinedLeftWord_envelope c e hc
  · exact qmaJoinedWord_envelope c e 3 hc
  · exact qmaJoinedWord_envelope a e 1 ha
  · exact qmaJoinedWord_envelope b e 1 hb

end ContinuumCoulomb

end

end OAI
