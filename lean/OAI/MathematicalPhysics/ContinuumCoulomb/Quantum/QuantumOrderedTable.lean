import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedCoefficient
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSupport

namespace OAI

/-! The literal support-list order indexes the small matrix table.  Its
Pauli coefficients agree with the actual ordered-history coefficients. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli Matrix
open scoped BigOperators Classical

theorem pauliWord_reindex {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (w : β → Fin 4)
    (s t : α → Fin 2) :
    qmaPauliWord (fun a => w (e a)) s t =
      qmaPauliWord w (fun b => s (e.symm b)) (fun b => t (e.symm b)) := by
  unfold qmaPauliWord
  simpa only [e.symm_apply_apply] using e.prod_comp
    (fun b => qmaPauli (w b) (s (e.symm b)) (t (e.symm b)))

theorem pauliCoefficient_reindex {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (A : Matrix (β → Fin 2) (β → Fin 2) ℂ) (w : β → Fin 4) :
    qmaPauliCoefficient
      (fun s t : α → Fin 2 => A (fun b => s (e.symm b)) (fun b => t (e.symm b)))
      (fun a => w (e a)) = qmaPauliCoefficient A w := by
  let E : (α → Fin 2) ≃ (β → Fin 2) := e.arrowCongr (Equiv.refl _)
  have hword (s t : α → Fin 2) :
      qmaPauliWord (fun a => w (e a)) t s = qmaPauliWord w (E t) (E s) :=
    pauliWord_reindex e w t s
  simp only [qmaPauliCoefficient,hword,Fintype.card_congr e]
  congr 1
  calc
    _ = ∑ s : α → Fin 2, ∑ t : β → Fin 2, A (E s) t*qmaPauliWord w t (E s) := by
      apply Finset.sum_congr rfl
      intro s _
      exact E.sum_comp (fun t => A (E s) t*qmaPauliWord w t (E s))
    _ = _ := E.sum_comp (fun s => ∑ t : β → Fin 2, A s t*qmaPauliWord w t s)

def orderedTable (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    Matrix (Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2)
      (Fin (QuantumOrderedSupport.sites c hT a).length → Fin 2) Scalar :=
  let e := QuantumOrderedSupport.supportEquiv c hT a
  fun s t => orderedCore c hT a (fun i => s (e.symm i)) (fun i => t (e.symm i))

def tableWord (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (w : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 4) :
    {i // i ∈ (qmaOrderedHistoryModel c hT).sites a} → Fin 4 :=
  fun i => w ((QuantumOrderedSupport.supportEquiv c hT a).symm i)

theorem orderedTable_coefficient (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c))
    (w : Fin (QuantumOrderedSupport.sites c hT a).length → Fin 4) :
    realValue (realCoefficient (orderedTable c hT a) w) =
      (qmaPauliCoefficient (qmaLocalCore ((qmaOrderedHistoryModel c hT).sites a)
        ((qmaOrderedHistoryModel c hT).matrix a)) (tableWord c hT a w)).re := by
  rw [realCoefficient_eq]
  let e := QuantumOrderedSupport.supportEquiv c hT a
  have hentries :
      (fun s t => value (orderedTable c hT a s t)) =
      (fun s t => qmaLocalCore ((qmaOrderedHistoryModel c hT).sites a)
        ((qmaOrderedHistoryModel c hT).matrix a)
          (fun i => s (e.symm i)) (fun i => t (e.symm i))) := by
    funext s t
    exact congrFun (congrFun (denote_orderedCore c hT a) _) _
  rw [hentries]
  have hw : (fun i => tableWord c hT a w (e i)) = w := by
    funext i
    simp only [tableWord,e,Equiv.symm_apply_apply]
  have hp := pauliCoefficient_reindex e
    (qmaLocalCore ((qmaOrderedHistoryModel c hT).sites a)
      ((qmaOrderedHistoryModel c hT).matrix a)) (tableWord c hT a w)
  rw [hw] at hp
  exact congrArg Complex.re hp

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
