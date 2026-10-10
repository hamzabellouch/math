import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleGraph
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathRelabeling

namespace OAI

/-! The selected-list ordering gives an explicit correspondence with the
abstract schedule's fresh spins. Retained source spins keep their labels. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open MediatorGraph

theorem active_source (s : State) (hs : Valid s) (i : Fin (partition true s.2.2).length) :
    s.2.2.get (qmaSelectedIndex (schedule s hs).active (activePermutation s hs i)) =
      (partition true s.2.2).get i := by
  have he : qmaSelectedIndex (schedule s hs).active (activePermutation s hs i) =
      (activeEquiv s hs i).val :=
    congrArg Subtype.val ((schedule s hs).active.equivFin.symm_apply_apply (activeEquiv s hs i))
  exact (congrArg (fun j : (schedule s hs).graph.Edge => s.2.2.get j) he).trans
    (indexEquiv_get true s.2.2 i)

theorem retained_source (s : State) (hs : Valid s) (i : Fin (partition false s.2.2).length) :
    s.2.2.get (retainedEquiv s hs i).val=(partition false s.2.2).get i :=
  indexEquiv_get false s.2.2 i

def vertexRelabel (s : State) (hs : Valid s) :
    Fin (s.1+(partition true s.2.2).length*2) ≃ Fin (s.1+(schedule s hs).active.card*2) :=
  ((vertexEquiv s.1 (partition true s.2.2).length).symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin s.1))
      (Equiv.prodCongr (activePermutation s hs) (Equiv.refl (Fin 2))))).trans
        (vertexEquiv s.1 (schedule s hs).active.card)

theorem vertexRelabel_old (s : State) (hs : Valid s) (v : Fin s.1) :
    vertexRelabel s hs (old s.1 (partition true s.2.2).length v) =
      old s.1 (schedule s hs).active.card v := by
  simp [vertexRelabel,old]

theorem vertexRelabel_fresh (s : State) (hs : Valid s)
    (i : Fin (partition true s.2.2).length) (a : Fin 2) :
    vertexRelabel s hs (fresh s.1 (partition true s.2.2).length i a) =
      fresh s.1 (schedule s hs).active.card (activePermutation s hs i) a := by
  simp [vertexRelabel,fresh]

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
