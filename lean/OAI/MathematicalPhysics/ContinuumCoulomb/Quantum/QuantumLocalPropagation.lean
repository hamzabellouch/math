import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalAction

namespace OAI

/-! Every guarded propagation term acts on three clock bits and at most two
computation bits. This is the actual unary-clock operator. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

abbrev QMACircuitQubit (c : QMACircuit) := Fin (c.gates.length+2) ⊕ Fin (c.work+1)

def qmaCircuitQubitSplit (c : QMACircuit) :
    (QMACircuitQubit c → Fin 2) ≃ QMAUnaryBasis c :=
  Equiv.sumArrowEquivProdArrow _ _ _

def qmaPropagationSites (c : QMACircuit) (t : Fin c.gates.length) : Finset (QMACircuitQubit c) :=
  {Sum.inl (qmaClockLeft c.gates.length t),Sum.inl (qmaClockMiddle c.gates.length t),
    Sum.inl (qmaClockRight c.gates.length t)} ∪
    (qmaGateSites c.work (c.gates.getD t.val (.hadamard 0))).map Function.Embedding.inr

theorem qmaPropagationSites_card (c : QMACircuit) (t : Fin c.gates.length) :
    (qmaPropagationSites c t).card ≤ 5 := by
  have h := Finset.card_union_le
    ({Sum.inl (qmaClockLeft c.gates.length t),Sum.inl (qmaClockMiddle c.gates.length t),
      Sum.inl (qmaClockRight c.gates.length t)} : Finset (QMACircuitQubit c))
    ((qmaGateSites c.work (c.gates.getD t.val (.hadamard 0))).map Function.Embedding.inr)
  have hclock : ({Sum.inl (qmaClockLeft c.gates.length t),
      Sum.inl (qmaClockMiddle c.gates.length t),Sum.inl (qmaClockRight c.gates.length t)} :
      Finset (QMACircuitQubit c)).card ≤ 3 := by
    apply le_trans (Finset.card_insert_le _ _)
    have h2 := Finset.card_insert_le (Sum.inl (qmaClockMiddle c.gates.length t))
      ({Sum.inl (qmaClockRight c.gates.length t)} : Finset (QMACircuitQubit c))
    simp only [Finset.card_singleton] at h2
    omega
  have hgate := qmaGateSites_card c.work (c.gates.getD t.val (.hadamard 0))
  simp only [Finset.card_map] at h
  unfold qmaPropagationSites
  omega

def qmaGuardProjection (c : QMACircuit) (t : Fin c.gates.length) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  Matrix.diagonal (fun s => if QMAClockGuard c.gates.length t (s ∘ Sum.inl) ∧
    s (Sum.inl (qmaClockMiddle c.gates.length t)) = 0 then 1 else 0)

def qmaLocalPropagationDelta (c : QMACircuit) (t : Fin c.gates.length) :
    Matrix (QMACircuitQubit c → Fin 2) (QMACircuitQubit c → Fin 2) ℂ :=
  qmaGuardProjection c t *
    (qmaBitFlipMatrix (Sum.inl (qmaClockMiddle c.gates.length t))-
      qmaJoinMatrix 1 (qmaStepMatrix c t.val))

theorem qmaGuardProjection_local (c : QMACircuit) (t : Fin c.gates.length) :
    QMALocalOn (qmaPropagationSites c t) (qmaGuardProjection c t) := by
  apply qmaLocalOn_diagonal
  intro s r h
  have hl := h (Sum.inl (qmaClockLeft c.gates.length t)) (by simp [qmaPropagationSites])
  have hm := h (Sum.inl (qmaClockMiddle c.gates.length t)) (by simp [qmaPropagationSites])
  have hr := h (Sum.inl (qmaClockRight c.gates.length t)) (by simp [qmaPropagationSites])
  simp only [QMAClockGuard,Function.comp_apply,hl,hm,hr]
  split_ifs with hp
  · exact (ite_eq_left hp).symm
  · exact (ite_eq_right hp).symm

theorem qmaLocalPropagationDelta_local (c : QMACircuit) (t : Fin c.gates.length) :
    QMALocalOn (qmaPropagationSites c t) (qmaLocalPropagationDelta c t) := by
  have hf := (qmaBitFlipMatrix_local (Sum.inl (qmaClockMiddle c.gates.length t))).mono
    (T := qmaPropagationSites c t)
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst i; simp [qmaPropagationSites])
  have hg := ((qmaGateMatrix_local c.work (c.gates.getD t.val (.hadamard 0))).joinRight
    (ι := Fin (c.gates.length+2))).mono (T := qmaPropagationSites c t) (Finset.subset_union_right)
  have hn := hg.smul (-1)
  have hs := hf.add hn
  simp only [neg_one_smul,←sub_eq_add_neg] at hs
  exact (qmaGuardProjection_local c t).mul hs

theorem qmaLocalPropagationGram_local (c : QMACircuit) (t : Fin c.gates.length) :
    QMALocalOn (qmaPropagationSites c t)
      ((qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t) :=
  (qmaLocalPropagationDelta_local c t).adjoint.mul (qmaLocalPropagationDelta_local c t)

end ContinuumCoulomb

end

end OAI
