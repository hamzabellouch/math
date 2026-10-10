import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListRound

namespace OAI

/-! Exact correspondence between the emitted ordered state and the finite
parallel-fork Hamiltonian. The mediator numbering is the proved prefix index. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumAxisSample QuantumRawExchange
open scoped BigOperators Classical

theorem retained_graph_list (s : State)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) :
    List.ofFn (fun a => erase
      (old s.1 (pairCount s.2.2.2) ((backgroundGraph s hb hn).left a),
       old s.1 (pairCount s.2.2.2) ((backgroundGraph s hb hn).right a),
       (backgroundGraph s hb hn).weight a)) = background s := by
  simpa only [backgroundGraph,QuantumListGraph.ofBonds,SourceBondLists.bonds,
    erase,MediatorIteration.old_val] using List.ofFn_get (background s)

theorem packet_graph_list (s : State) (hs : ValidPorts s.1 s.2.2.2) (R : ℚ) :
    (List.ofFn (fun e => packetBonds e (actualSite hs e)
      (actualJ s.2.2.2 e) (actualK s.2.2.2 e) R)).flatten=packets s R := by
  unfold packets
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < pairCount s.2.2.2 := by simpa only [List.length_ofFn] using hi
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
    rw [catalog_actualSite hs ⟨i,hi'⟩]
    rfl

theorem graph_bonds_eq (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (R : ℚ) :
    graphBonds (backgroundGraph s hb hn).left (backgroundGraph s hb hn).right
      (backgroundGraph s hb hn).weight (actualSite hs) (actualJ s.2.2.2)
      (actualK s.2.2.2) R = background s++packets s R := by
  unfold graphBonds
  exact congrArg₂ List.append (retained_graph_list s hb hn) (packet_graph_list s hs R)

theorem next_constant (s : State) (N : ℚ) :
    (next N s).2.2.1 = graphConstant s.2.2.1 (scale N s)
      (actualJ s.2.2.2) (actualK s.2.2.2) := by
  have h : (((catalog s.2.2.2).map Prod.snd).map pairOffset).sum =
      ∑ e, (3/4+3*(actualJ s.2.2.2 e)^2+3*(actualK s.2.2.2 e)^2) :=
    catalog_weights_sum s.2.2.2 (fun J K => 3/4+3*J^2+3*K^2)
  dsimp only [next,graphConstant]
  rw [h]

def rawBottom (n : ℕ) (out : List MediatorListProgram.Bond × ℚ) : ℝ :=
  normalizedBottom (rawMatrix n out)

theorem next_bottom_graph (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) :
    normalizedBottom (matrix (next N s)) =
      normalizedBottom (qmaForksGraph (backgroundGraph s hb hn).left (backgroundGraph s hb hn).right
        (fun e => ((backgroundGraph s hb hn).weight e:ℝ)) (s.2.2.1:ℝ) (scale N s:ℝ)
        (actualSite hs) (fun e => (actualJ s.2.2.2 e:ℝ)) (fun e => (actualK s.2.2.2 e:ℝ))) := by
  rw [next_matrix_packets,next_constant]
  change rawBottom (s.1+2*pairCount s.2.2.2)
    (background s++packets s (scale N s),
      graphConstant s.2.2.1 (scale N s) (actualJ s.2.2.2) (actualK s.2.2.2)) = _
  rw [show s.1+2*pairCount s.2.2.2=s.1+pairCount s.2.2.2*2 by omega]
  unfold rawBottom
  rw [← graph_bonds_eq s hs hb hn]
  exact congrArg normalizedBottom (graph_matrix _ _ _ _ _ _ _ _)

end ContinuumCoulomb.QuantumForkList

end

end OAI
