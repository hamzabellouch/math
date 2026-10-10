import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumTaggedStage

namespace OAI

/-! Every column label gives an explicit bounded spatial support for its gate. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def QMALocatedGate (rows width : ℕ) (r : Fin (rows+1)) (j : Fin (width+1)) (g : QMAGate) : Prop :=
  ∀ k ∈ qmaGateSites (qmaGridWork rows width) g,
    ∃ s : Fin (rows+1), ∃ i : Fin (width+1),
      k = qmaGridQubit rows width s i ∧ r.val ≤ s.val ∧ s.val ≤ r.val+1 ∧
        i.val ≤ j.val+1 ∧ j.val ≤ i.val+1

theorem qmaColumnTransfer_located (rows width : ℕ) (r : Fin rows)
    (cols : List (Fin (width+1))) (g : QMAGate) (j : Fin (width+1))
    (h : (g,j) ∈ qmaColumnTransfer (qmaGridQubit rows width r.castSucc)
      (qmaGridQubit rows width r.succ) cols) :
    QMALocatedGate rows width r.castSucc j g := by
  obtain ⟨_,hg⟩ := qmaColumnTransfer_member _ _ _ _ _ h
  intro k hk
  rcases qmaWireSwap_sites _ _ g hg k hk with rfl | rfl
  · exact ⟨r.castSucc,j,rfl,le_rfl,by simp,by omega,by omega⟩
  · exact ⟨r.succ,j,rfl,by simp,by simp,by omega,by omega⟩

theorem qmaTaggedRowStage_located (rows width : ℕ) (r : Fin rows)
    (e : Equiv.Perm (Fin (width+1))) (g : QMAGate)
    (hg : g.WellFormed (width+1)) (ha : g.Adjacent)
    (k : QMAGate) (j : Fin (width+1))
    (hk : (k,j) ∈ qmaTaggedRowStage width (qmaGridWork rows width)
      (qmaGridQubit rows width r.castSucc) (qmaGridQubit rows width r.succ) e g) :
    QMALocatedGate rows width r.castSucc j k := by
  simp only [qmaTaggedRowStage,List.mem_append,List.mem_singleton] at hk
  rcases hk with (hk | hk) | hk
  · exact qmaColumnTransfer_located rows width r _ k j hk
  · have he1 := congrArg Prod.fst hk
    have he2 := congrArg Prod.snd hk
    dsimp only at he1 he2
    subst k
    subst j
    intro v hv
    rw [qmaMapGate_sites] at hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    have hn := qmaGateArrivalColumn_near width e g hg ha i hi
    exact ⟨r.succ,i,rfl,by simp,by simp,hn.1,hn.2⟩
  · exact qmaColumnTransfer_located rows width r _ k j hk

end ContinuumCoulomb

end

end OAI
