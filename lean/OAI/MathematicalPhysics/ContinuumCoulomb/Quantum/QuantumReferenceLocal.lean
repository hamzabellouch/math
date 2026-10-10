import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceReal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLocalJoin

namespace OAI

/-! A separate reference qubit adds exactly one site to each original support. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QMALocalOn.entryReal {S : Finset ι}
    {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} (hA : QMALocalOn S A) :
    QMALocalOn S (qmaEntryReal A) := by
  obtain ⟨B,rfl⟩ := hA
  refine ⟨qmaEntryReal B,?_⟩
  ext s t
  simp only [qmaEntryReal,qmaLocalLift_apply]
  split_ifs <;> simp

theorem QMALocalOn.entryImag {S : Finset ι}
    {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} (hA : QMALocalOn S A) :
    QMALocalOn S (qmaEntryImag A) := by
  obtain ⟨B,rfl⟩ := hA
  refine ⟨qmaEntryImag B,?_⟩
  ext s t
  simp only [qmaEntryImag,qmaLocalLift_apply]
  split_ifs <;> simp

theorem qmaLocalY_local (n : ℕ) (i : Fin n) :
    QMALocalOn {i} (sourceLocalPauli n i 1) := by
  apply qmaLocalOn_sourceTensor
  intro k hk
  simp only [Finset.mem_singleton] at hk
  simp [hk]

def qmaDistributedRebitSites (n : ℕ) (i : Fin n) (S : Finset ι) : Finset (Fin n ⊕ ι) :=
  insert (Sum.inl i) (S.map Function.Embedding.inr)

def qmaDistributedRebitOnQubits (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    Matrix (Fin n ⊕ ι → Fin 2) (Fin n ⊕ ι → Fin 2) ℂ :=
  (qmaDistributedRebitTerm n i A).submatrix
    (Equiv.sumArrowEquivProdArrow (Fin n) ι (Fin 2))
    (Equiv.sumArrowEquivProdArrow (Fin n) ι (Fin 2))

theorem qmaDistributedRebitOnQubits_eq (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    qmaDistributedRebitOnQubits n i A =
      qmaJoinMatrix (ι := Fin n) 1 (qmaEntryReal A)+
      (-Complex.I) • qmaJoinMatrix (sourceLocalPauli n i 1) (qmaEntryImag A) := by
  ext s t
  rfl

theorem qmaDistributedRebitOnQubits_local (n : ℕ) (i : Fin n) {S : Finset ι}
    {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} (hA : QMALocalOn S A) :
    QMALocalOn (qmaDistributedRebitSites n i S) (qmaDistributedRebitOnQubits n i A) := by
  rw [qmaDistributedRebitOnQubits_eq]
  apply QMALocalOn.add
  · exact hA.entryReal.joinRight.mono (Finset.subset_insert _ _)
  · have h := (qmaLocalY_local n i).join hA.entryImag
    have he : (({i} : Finset (Fin n)).map (Function.Embedding.inl : Fin n ↪ Fin n ⊕ ι) ∪
        S.map Function.Embedding.inr) = qmaDistributedRebitSites n i S := by
      simp [qmaDistributedRebitSites]
    rw [he] at h
    exact h.smul _

omit [Fintype ι] in
theorem qmaDistributedRebitSites_card (n : ℕ) (i : Fin n) (S : Finset ι) :
    (qmaDistributedRebitSites n i S).card = S.card+1 := by
  simp [qmaDistributedRebitSites]

omit [Fintype ι] [DecidableEq ι] in
theorem qmaDistributedRebitOnQubits_real (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (s t : Fin n ⊕ ι → Fin 2) :
    (qmaDistributedRebitOnQubits n i A s t).im = 0 :=
  qmaDistributedRebitTerm_real _ _ _ _ _

theorem qmaDistributedRebitOnQubits_hermitian (n : ℕ) (i : Fin n)
    (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (hA : A.IsHermitian) :
    (qmaDistributedRebitOnQubits n i A).IsHermitian :=
  (qmaDistributedRebitTerm_hermitian n i A hA).submatrix _

end ContinuumCoulomb

end

end OAI
