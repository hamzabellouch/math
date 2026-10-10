import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepCongestion

namespace OAI

/-! Every physical row is touched in a nonempty sweep, including the final row. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaRowStage_containsSwap (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g k : QMAGate) (i : Fin (width+1)) (hk : k ∈ qmaWireSwapGates (l i) (r i)) :
    k ∈ qmaRowStage width work l r e g := by
  let ps := qmaRowPairs (l ∘ e) (r ∘ e)
  have hp : (l i,r i) ∈ ps := by
    exact List.mem_ofFn.mpr ⟨e.symm i,by simp⟩
  have hcases : (l i,r i) ∈ ps.take (qmaGateCut width e g) ∨
      (l i,r i) ∈ ps.drop (qmaGateCut width e g) := by
    rw [←List.mem_append,List.take_append_drop]
    exact hp
  change k ∈ qmaTransferGates (ps.take (qmaGateCut width e g)) ++ [_] ++
    qmaTransferGates (ps.drop (qmaGateCut width e g))
  rcases hcases with hp | hp
  · exact List.mem_append_left _ (List.mem_append_left _
      ((qmaTransferGates_member _ k).mpr ⟨_,hp,hk⟩))
  · exact List.mem_append_right _ ((qmaTransferGates_member _ k).mpr ⟨_,hp,hk⟩)

theorem qmaGridStage_touches (rows width : ℕ) (r : Fin rows)
    (e : Equiv.Perm (Fin (width+1))) (g : QMAGate) (j : Fin (width+1)) :
    ∃ k ∈ qmaRowStage width (qmaGridWork rows width)
      (qmaGridQubit rows width r.castSucc) (qmaGridQubit rows width r.succ) e g,
      qmaGridQubit rows width r.castSucc j ∈ qmaGateSites (qmaGridWork rows width) k ∧
      qmaGridQubit rows width r.succ j ∈ qmaGateSites (qmaGridWork rows width) k := by
  let a := qmaGridQubit rows width r.castSucc j
  let b := qmaGridQubit rows width r.succ j
  refine ⟨.controlledNot a.val b.val,?_,?_⟩
  · apply qmaRowStage_containsSwap _ _ _ _ _ g _ j
    simp [qmaWireSwapGates,a,b]
  · simp [qmaGateSites,qmaQubit_fin,a,b]

theorem qmaSweepCircuitFrom_touches (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) (hne : gs ≠ [])
    (q : Fin (rows+1)) (hq : start ≤ q.val) (hq' : q.val ≤ start+gs.length)
    (j : Fin (width+1)) :
    ∃ k ∈ qmaSweepCircuitFrom rows width start gs h,
      qmaGridQubit rows width q j ∈ qmaGateSites (qmaGridWork rows width) k := by
  induction gs generalizing start with
  | nil => exact False.elim (hne rfl)
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    by_cases hnear : q.val ≤ start+1
    · obtain ⟨k,hk,hl,hr⟩ := qmaGridStage_touches rows width ⟨start,hs⟩
        (qmaSweepOrder width (rows-1-start)) g j
      refine ⟨k,List.mem_append_left _ hk,?_⟩
      have hqcases : q = (⟨start,hs⟩ : Fin rows).castSucc ∨
          q = (⟨start,hs⟩ : Fin rows).succ := by
        have : q.val = start ∨ q.val = start+1 := by omega
        exact this.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
      rcases hqcases with rfl | rfl
      · exact hl
      · exact hr
    · have htail : gs ≠ [] := by
        intro he
        simp only [he,List.length_cons,List.length_nil] at hq'
        omega
      obtain ⟨k,hk,hv⟩ := ih (start+1) (by simp only [List.length_cons] at h; omega)
        htail (by omega) (by simp only [List.length_cons] at hq'; omega)
      exact ⟨k,List.mem_append_right _ hk,hv⟩

theorem qmaGridQubit_surjective (rows width : ℕ) :
    Function.Surjective (fun p : Fin (rows+1) × Fin (width+1) => qmaGridQubit rows width p.1 p.2) := by
  apply ((Fintype.bijective_iff_injective_and_card _).mpr ⟨qmaGridQubit_injective rows width,?_⟩).2
  simp only [Fintype.card_prod,Fintype.card_fin]
  unfold qmaGridWork
  ring

theorem qmaSweepCircuit_touches (c : QMACircuit) (hne : c.gates ≠ [])
    (i : Fin ((qmaSweepCircuit c).work+1)) :
    ∃ g ∈ (qmaSweepCircuit c).gates, i ∈ qmaGateSites (qmaSweepCircuit c).work g := by
  obtain ⟨⟨r,j⟩,he⟩ := qmaGridQubit_surjective c.gates.length c.work i
  rw [←he]
  exact qmaSweepCircuitFrom_touches _ _ _ _ _ hne r (by omega) (by have := r.isLt; omega) j

end ContinuumCoulomb

end

end OAI
