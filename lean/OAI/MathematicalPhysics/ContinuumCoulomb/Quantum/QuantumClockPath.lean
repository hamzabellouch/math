import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumStagePath

namespace OAI

/-! The full literal clock path has bounded steps, including every row transition. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaTaggedSweepFrom_head (rows width start : ℕ) (g : QMAGate) (gs : List QMAGate)
    (h : start+(g::gs).length ≤ rows) :
    (qmaTaggedSweepFrom rows width start (g::gs) h).head?.map Prod.snd =
      some ((⟨start,by simp only [List.length_cons] at h; omega⟩ : Fin (rows+1)),
        qmaSweepOrder width (rows-1-start) 0) := by
  have hs : start < rows := by simp only [List.length_cons] at h; omega
  change ((qmaGridStageTags rows width ⟨start,hs⟩ (qmaSweepOrder width (rows-1-start)) g) ++
    qmaTaggedSweepFrom rows width (start+1) gs _).head?.map Prod.snd = _
  rw [List.head?_append_of_ne_nil _ (qmaGridStageTags_nonempty _ _ _ _ _)]
  exact qmaGridStageTags_head _ _ _ _ _

theorem qmaTaggedSweepFrom_chain (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows) :
    (qmaTaggedSweepFrom rows width start gs h).IsChain QMAGridTagNear := by
  induction gs generalizing start with
  | nil => exact List.IsChain.nil
  | cons g gs ih =>
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    let r : Fin rows := ⟨start,hs⟩
    change (qmaGridStageTags rows width r (qmaSweepOrder width (rows-1-start)) g ++
      qmaTaggedSweepFrom rows width (start+1) gs _).IsChain QMAGridTagNear
    apply List.IsChain.append (qmaGridStageTags_chain rows width r g) (ih (start+1) _)
    intro x hx y hy
    cases gs with
    | nil => simp [qmaTaggedSweepFrom] at hy
    | cons g' gs' =>
      have hlast := qmaGridStageTags_last rows width r (qmaSweepOrder width (rows-1-start)) g
      have hhead := qmaTaggedSweepFrom_head rows width (start+1) g' gs' (by
        simp only [List.length_cons] at h ⊢; omega)
      have hx' := Option.mem_map_of_mem Prod.snd hx
      have hy' := Option.mem_map_of_mem Prod.snd hy
      rw [hlast] at hx'
      rw [hhead] at hy'
      have hxc := (Option.mem_some_iff.mp hx').symm
      have hyc := (Option.mem_some_iff.mp hy').symm
      have hrow : 0 < rows-1-start := by simp only [List.length_cons] at h; omega
      have hturn := qmaSweepOrder_turn width (rows-1-start) hrow
      have he : rows-1-start-1 = rows-1-(start+1) := by omega
      rw [he] at hturn
      unfold QMAGridTagNear
      rw [hxc,hyc]
      change start ≤ start+1+1 ∧ start+1 ≤ start+1 ∧
        (qmaSweepOrder width (rows-1-start) (Fin.last width)).val ≤
          (qmaSweepOrder width (rows-1-(start+1)) 0).val+1 ∧
        (qmaSweepOrder width (rows-1-(start+1)) 0).val ≤
          (qmaSweepOrder width (rows-1-start) (Fin.last width)).val+1
      rw [hturn]
      exact ⟨by omega,le_rfl,by omega,by omega⟩

theorem qmaSparseTags_chain (c : QMACircuit) : (qmaSparseTags c).IsChain QMAGridTagNear :=
  qmaTaggedSweepFrom_chain _ _ _ _ _

end ContinuumCoulomb

end

end OAI
