import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPaddedLocal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliRounding

namespace OAI

/-! A literal 4096-word family for each actual ordered history term.  The
term type is a product, so its emitted order requires no filtered finite type. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedHistory
open QuantumAlgebraicHistory
open scoped BigOperators Classical

abbrev Term (c : QMACircuit) :=
  QMAReferenceTerm (qmaHistoryReferenceWork c) × (Fin 6 → Fin 4)

def widthIndex (n : ℕ) (hn : n ≤ 6) :
    (Fin 6 → Fin 4) ≃ (Fin (n+(6-n)) → Fin 4) :=
  Equiv.cast (by rw [Nat.add_sub_of_le hn])

def tableMatrix (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :=
  denote (orderedTable c hT a)

theorem tableMatrix_eq (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    tableMatrix c hT a =
      (qmaLocalCore ((qmaOrderedHistoryModel c hT).sites a)
        ((qmaOrderedHistoryModel c hT).matrix a)).submatrix
        (fun s i => s ((QuantumOrderedSupport.supportEquiv c hT a).symm i))
        (fun s i => s ((QuantumOrderedSupport.supportEquiv c hT a).symm i)) := by
  ext s t
  exact congrFun (congrFun (denote_orderedCore c hT a) _) _

theorem tableMatrix_hermitian (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    (tableMatrix c hT a).IsHermitian := by
  rw [tableMatrix_eq]
  exact (qmaLocalCore_hermitian _ _ ((qmaOrderedHistoryModel c hT).hermitian a)).submatrix _

theorem tableMatrix_real (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) (s t) :
    (tableMatrix c hT a s t).im = 0 := by
  rw [tableMatrix_eq]
  exact qmaLocalCore_real _ _ ((qmaOrderedHistoryModel c hT).real a) _ _

def word (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    (qmaOrderedHistoryModel c hT).Q → Fin 4 :=
  QuantumPaddedLocal.word ((qmaOrderedHistoryModel c hT).sites p.1)
    (QuantumOrderedSupport.supportEquiv c hT p.1)
    (6-(QuantumOrderedSupport.sites c hT p.1).length)
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2)

def coefficient (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) : ℝ :=
  QuantumPaddedPauli.paddedCoefficient
    (QuantumOrderedSupport.sites c hT p.1).length
    (6-(QuantumOrderedSupport.sites c hT p.1).length)
    (tableMatrix c hT p.1)
    (widthIndex _ (QuantumOrderedSupport.sites_length c hT p.1) p.2)

theorem term_sum (c : QMACircuit) (hT : 0 < c.gates.length)
    (a : QMAReferenceTerm (qmaHistoryReferenceWork c)) :
    (∑ w : Fin 6 → Fin 4, (coefficient c hT (a,w):ℂ) •
      qmaPauliWord (word c hT (a,w))) = (qmaOrderedHistoryModel c hT).matrix a := by
  let n := (QuantumOrderedSupport.sites c hT a).length
  let S : Finset (QuantumOrderedSupport.Qubit c) := (qmaOrderedHistoryModel c hT).sites a
  let e : Fin n ≃ {i // i ∈ S} := QuantumOrderedSupport.supportEquiv c hT a
  let A := tableMatrix c hT a
  let f : (Fin (n+(6-n)) → Fin 4) →
      Matrix (QuantumOrderedSupport.Qubit c → Fin 2) (QuantumOrderedSupport.Qubit c → Fin 2) ℂ :=
    fun v => (QuantumPaddedPauli.paddedCoefficient n (6-n) A v:ℂ) •
      qmaPauliWord (QuantumPaddedLocal.word S e (6-n) v)
  have hsum := (widthIndex n (QuantumOrderedSupport.sites_length c hT a)).sum_comp f
  have hfull := QuantumPaddedLocal.full_expansion S e (6-n) A
    (tableMatrix_hermitian c hT a) (tableMatrix_real c hT a)
  have he : QuantumPaddedLocal.reindex S e A =
        qmaLocalCore ((qmaOrderedHistoryModel c hT).sites a)
          ((qmaOrderedHistoryModel c hT).matrix a) := by
    dsimp only [A]
    rw [tableMatrix_eq]
    ext s t
    simp only [QuantumPaddedLocal.reindex,Matrix.submatrix_apply,
      e]
    apply congrArg₂ _
    · funext i
      exact congrArg s ((QuantumOrderedSupport.supportEquiv c hT a).apply_symm_apply i)
    · funext i
      exact congrArg t ((QuantumOrderedSupport.supportEquiv c hT a).apply_symm_apply i)
  have hend : qmaLocalLift S (QuantumPaddedLocal.reindex S e A) =
      (qmaOrderedHistoryModel c hT).matrix a := by
    rw [he]
    exact ((qmaOrderedHistoryModel c hT).localOn a).core_lift
  exact hsum.trans (hfull.trans hend)

theorem family_sum (c : QMACircuit) (hT : 0 < c.gates.length) :
    qmaPauliFamily (word c hT) (coefficient c hT) =
      ∑ a, (qmaOrderedHistoryModel c hT).matrix a := by
  rw [qmaPauliFamily,Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun a _ => term_sum c hT a)

theorem term_count (c : QMACircuit) :
    Fintype.card (Term c) = 4096*(4*c.gates.length+2*c.work+9) := by
  simp only [Term,QMAReferenceTerm,Fintype.card_prod,Fintype.card_sum,
    Fintype.card_fin,Fintype.card_fun,qmaHistoryReferenceWork]
  ring

theorem support (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    qmaPauliSupport (word c hT p) ⊆ (qmaOrderedHistoryModel c hT).sites p.1 :=
  QuantumPaddedLocal.word_support _ _ _ _

theorem even (c : QMACircuit) (hT : 0 < c.gates.length) (p : Term c) :
    Even (qmaPauliYCount (word c hT p)) :=
  QuantumPaddedLocal.word_even _ _ _ _

end ContinuumCoulomb.QuantumPaddedHistory

end

end OAI
