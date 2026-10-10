import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRowInsertion

namespace OAI

/-! The insertion keeps the exact stage size and well-formed gate set. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaRowStage_length (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) : (qmaRowStage width work l r e g).length = 3*(width+1)+1 := by
  let ps := qmaRowPairs (l ∘ e) (r ∘ e)
  have hs : (ps.take (qmaGateCut width e g)).length+
      (ps.drop (qmaGateCut width e g)).length = width+1 := by
    rw [←List.length_append,List.take_append_drop]
    simp [ps,qmaRowPairs]
  change (qmaTransferGates (ps.take (qmaGateCut width e g)) ++
    [qmaMapGate width work r g] ++ qmaTransferGates (ps.drop (qmaGateCut width e g))).length = _
  simp only [List.length_append,List.length_singleton,qmaTransferGates_length]
  omega

theorem qmaRowStage_wellFormed (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (hr : Function.Injective r)
    (hlr : ∀ i j, l i ≠ r j) (e : Equiv.Perm (Fin (width+1)))
    (g : QMAGate) (hg : g.WellFormed (width+1)) :
    ∀ k ∈ qmaRowStage width work l r e g, k.WellFormed (work+1) := by
  have hp := qmaRowPairs_distinct (l ∘ e) (r ∘ e) (fun i j => hlr (e i) (e j))
  intro k hk
  simp only [qmaRowStage,List.mem_append,List.mem_singleton] at hk
  rcases hk with (hk | rfl) | hk
  · exact qmaTransferGates_wellFormed _
      (fun p hm => hp p (List.mem_of_mem_take hm)) k hk
  · exact qmaMapGate_wellFormed width work r hr g hg
  · exact qmaTransferGates_wellFormed _
      (fun p hm => hp p (List.mem_of_mem_drop hm)) k hk

end ContinuumCoulomb

end

end OAI
