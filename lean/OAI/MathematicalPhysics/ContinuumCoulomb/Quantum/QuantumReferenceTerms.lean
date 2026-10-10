import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceEdges

namespace OAI

/-! The full reference Hamiltonian as explicit bounded-support real terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev QMAReferenceTerm (n : ℕ) := Fin (n+1) ⊕ Fin n

def qmaReferenceTermMatrix (n : ℕ)
    (A : Fin (n+1) → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    QMAReferenceTerm n → Matrix (Fin (n+1) ⊕ ι → Fin 2) (Fin (n+1) ⊕ ι → Fin 2) ℂ
  | .inl i => qmaDistributedRebitOnQubits (n+1) i (A i)
  | .inr i => qmaReferenceEdgeOnQubits n i

def qmaReferenceTermSites (n : ℕ) (S : Fin (n+1) → Finset ι) :
    QMAReferenceTerm n → Finset (Fin (n+1) ⊕ ι)
  | .inl i => qmaDistributedRebitSites (n+1) i (S i)
  | .inr i => qmaReferenceEdgeSites n i

def qmaReferenceOnQubits (n : ℕ)
    (A : Fin (n+1) → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :=
  (qmaReferenceFamily n A 1).submatrix
    (Equiv.sumArrowEquivProdArrow (Fin (n+1)) ι (Fin 2))
    (Equiv.sumArrowEquivProdArrow (Fin (n+1)) ι (Fin 2))

theorem qmaReferenceTerm_sum (n : ℕ)
    (A : Fin (n+1) → Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    (∑ t, qmaReferenceTermMatrix n A t) = qmaReferenceOnQubits n A := by
  ext s t
  simp only [Fintype.sum_sum_type,Matrix.add_apply,Matrix.sum_apply,qmaReferenceTermMatrix,
    qmaReferenceOnQubits,qmaReferenceFamily,Matrix.submatrix_apply,Complex.ofReal_one,one_smul,qmaReferenceYPenalty]
  change (∑ i, qmaDistributedRebitOnQubits (n+1) i (A i) s t)+
    (∑ i, qmaReferenceEdgeOnQubits n i s t) =
    (∑ i, qmaDistributedRebitOnQubits (n+1) i (A i) s t)+
    ((∑ i, qmaReferenceYEdge n i) (s ∘ Sum.inl) (t ∘ Sum.inl))*
      (1 : Matrix (ι → Fin 2) _ ℂ) (s ∘ Sum.inr) (t ∘ Sum.inr)
  simp only [Matrix.sum_apply,Finset.sum_mul]
  rfl

theorem qmaReferenceTerm_local (n : ℕ)
    (A : Fin (n+1) → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (S : Fin (n+1) → Finset ι) (hA : ∀ i, QMALocalOn (S i) (A i))
    (t : QMAReferenceTerm n) :
    QMALocalOn (qmaReferenceTermSites n S t) (qmaReferenceTermMatrix n A t) := by
  cases t with
  | inl i => exact qmaDistributedRebitOnQubits_local _ _ (hA i)
  | inr i => exact qmaReferenceEdgeOnQubits_local _ _

omit [Fintype ι] in
theorem qmaReferenceTerm_card (n : ℕ) (S : Fin (n+1) → Finset ι)
    (hS : ∀ i, (S i).card ≤ 5) (t : QMAReferenceTerm n) :
    (qmaReferenceTermSites n S t).card ≤ 6 := by
  cases t with
  | inl i =>
    change (qmaDistributedRebitSites (n+1) i (S i)).card ≤ 6
    rw [qmaDistributedRebitSites_card]
    have := hS i
    omega
  | inr i =>
    change ({Sum.inl i.castSucc,Sum.inl i.succ} : Finset (Fin (n+1) ⊕ ι)).card ≤ 6
    have h := Finset.card_insert_le (Sum.inl i.castSucc)
      ({Sum.inl i.succ} : Finset (Fin (n+1) ⊕ ι))
    simp only [Finset.card_singleton] at h
    omega

theorem qmaReferenceTerm_hermitian (n : ℕ)
    (A : Fin (n+1) → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hA : ∀ i, (A i).IsHermitian) (t : QMAReferenceTerm n) :
    (qmaReferenceTermMatrix n A t).IsHermitian := by
  cases t with
  | inl i => exact qmaDistributedRebitOnQubits_hermitian _ _ _ (hA i)
  | inr i => exact qmaReferenceEdgeOnQubits_hermitian _ _

theorem qmaReferenceTerm_real (n : ℕ)
    (A : Fin (n+1) → Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (t : QMAReferenceTerm n) (s u : Fin (n+1) ⊕ ι → Fin 2) :
    (qmaReferenceTermMatrix n A t s u).im = 0 := by
  cases t with
  | inl i => exact qmaDistributedRebitOnQubits_real _ _ _ _ _
  | inr i => exact qmaReferenceEdgeOnQubits_real _ _ _ _

end ContinuumCoulomb

end

end OAI
