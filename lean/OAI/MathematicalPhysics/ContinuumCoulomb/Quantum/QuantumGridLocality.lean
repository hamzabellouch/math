import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRowStageSupport

namespace OAI

/-! A concrete polynomial-size verifier with geometrically local computation gates. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def QMAGridLocal (rows width : ℕ) (g : QMAGate) : Prop :=
  ∃ r : Fin (rows+1), ∃ lo : Fin (width+1), ∀ k ∈ qmaGateSites (qmaGridWork rows width) g,
    ∃ s : Fin (rows+1), ∃ j : Fin (width+1),
      k = qmaGridQubit rows width s j ∧ r.val ≤ s.val ∧ s.val ≤ r.val+1 ∧
        lo.val ≤ j.val ∧ j.val ≤ lo.val+1

theorem qmaRowStage_gridLocal (rows width : ℕ) (r : Fin rows)
    (e : Equiv.Perm (Fin (width+1))) (g : QMAGate)
    (hg : g.WellFormed (width+1)) (ha : g.Adjacent) (k : QMAGate)
    (hk : k ∈ qmaRowStage width (qmaGridWork rows width)
      (qmaGridQubit rows width r.castSucc) (qmaGridQubit rows width r.succ) e g) :
    QMAGridLocal rows width k := by
  rcases qmaRowStage_member _ _ _ _ _ g k hk with rfl | ⟨i,hi⟩
  · obtain ⟨lo,hlo⟩ := qmaAdjacentGate_window width g hg ha
    refine ⟨r.castSucc,lo,?_⟩
    intro k hk
    rw [qmaMapGate_sites] at hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    exact ⟨r.succ,j,rfl,by simp,by simp,(hlo j hj).1,(hlo j hj).2⟩
  · refine ⟨r.castSucc,i,?_⟩
    intro v hv
    rcases qmaWireSwap_sites _ _ k hi v hv with rfl | rfl
    · exact ⟨r.castSucc,i,rfl,le_rfl,by simp,le_rfl,by omega⟩
    · exact ⟨r.succ,i,rfl,by simp,by simp,le_rfl,by omega⟩

theorem qmaSweepCircuitFrom_local (rows width start : ℕ) (gs : List QMAGate)
    (h : start+gs.length ≤ rows)
    (hg : ∀ g ∈ gs, g.WellFormed (width+1)) (ha : ∀ g ∈ gs, g.Adjacent) :
    ∀ k ∈ qmaSweepCircuitFrom rows width start gs h, QMAGridLocal rows width k := by
  induction gs generalizing start with
  | nil => simp [qmaSweepCircuitFrom]
  | cons g gs ih =>
    intro k hk
    have hs : start < rows := by simp only [List.length_cons] at h; omega
    have ht : start+1+gs.length ≤ rows := by simp only [List.length_cons] at h; omega
    rcases List.mem_append.mp hk with hk | hk
    · exact qmaRowStage_gridLocal rows width ⟨start,hs⟩ _ g
        (hg g (by simp)) (ha g (by simp)) k hk
    · exact ih (start+1) ht (fun k hk => hg k (by simp [hk]))
        (fun k hk => ha k (by simp [hk])) k hk

theorem qmaSweepCircuit_size (c : QMACircuit) :
    (qmaSweepCircuit c).work+(qmaSweepCircuit c).gates.length =
      c.work+(4*c.work+5)*c.gates.length := by
  change qmaGridWork c.gates.length c.work+
    (qmaSweepCircuitFrom c.gates.length c.work 0 c.gates _).length = _
  rw [qmaSweepCircuitFrom_length]
  unfold qmaGridWork
  ring

abbrev qmaSparseCircuit (c : QMACircuit) : QMACircuit := qmaSweepCircuit (qmaNearestCircuit c)

theorem qmaSparseCircuit_wellFormed (c : QMACircuit) (hc : c.WellFormed) :
    (qmaSparseCircuit c).WellFormed :=
  qmaSweepCircuit_wellFormed (qmaNearestCircuit c) (qmaNearestCircuit_wellFormed c hc)

theorem qmaSparseCircuit_acceptance (c : QMACircuit) (hc : c.WellFormed)
    (psi : EuclideanSpace ℂ (SourceSpinBasis c.witness)) :
    qmaAcceptance (qmaSparseCircuit c) (qmaSparseCircuit_wellFormed c hc) psi =
      qmaAcceptance c hc psi := by
  rw [qmaSweepCircuit_acceptance (qmaNearestCircuit c) (qmaNearestCircuit_wellFormed c hc),
    qmaNearestCircuit_acceptance c hc]

theorem qmaSparseCircuit_local (c : QMACircuit) (hc : c.WellFormed) :
    ∀ g ∈ (qmaSparseCircuit c).gates,
      QMAGridLocal (qmaNearestCircuit c).gates.length c.work g :=
  qmaSweepCircuitFrom_local _ _ _ _ _ (qmaNearestCircuit_wellFormed c hc).2
    (qmaNearestCircuit_adjacent c hc)

theorem qmaSparseCircuit_size (c : QMACircuit) :
    (qmaSparseCircuit c).work+(qmaSparseCircuit c).gates.length ≤
      c.work+(4*c.work+5)*(6*c.work+7)*c.gates.length := by
  rw [qmaSweepCircuit_size]
  exact Nat.add_le_add_left (by
    simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_left (4*c.work+5) (qmaNearestList_length c.work c.gates)) c.work

end ContinuumCoulomb

end

end OAI
