import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceLocal

namespace OAI

/-! The reference alignment penalty is a sum of real two-site interactions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Kronecker Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaReferenceYEdge (n : ℕ) (i : Fin n) :
    Matrix (SourceSpinBasis (n+1)) (SourceSpinBasis (n+1)) ℂ :=
  (1/2 : ℂ) • (1-sourceLocalPauli (n+1) i.castSucc 1*sourceLocalPauli (n+1) i.succ 1)

theorem qmaReferenceYEdge_local (n : ℕ) (i : Fin n) :
    QMALocalOn {i.castSucc,i.succ} (qmaReferenceYEdge n i) := by
  have ha := (qmaLocalY_local (n+1) i.castSucc).mono (by simp :
    ({i.castSucc} : Finset (Fin (n+1))) ⊆ {i.castSucc,i.succ})
  have hb := (qmaLocalY_local (n+1) i.succ).mono (by simp :
    ({i.succ} : Finset (Fin (n+1))) ⊆ {i.castSucc,i.succ})
  have h1 : QMALocalOn {i.castSucc,i.succ} (1 : Matrix (SourceSpinBasis (n+1)) _ ℂ) :=
    ⟨1,(qmaLocalLift_one _).symm⟩
  simpa only [qmaReferenceYEdge,sub_eq_add_neg,neg_one_smul] using
    (h1.add ((ha.mul hb).smul (-1))).smul (1/2 : ℂ)

theorem qmaReferenceYEdge_real (n : ℕ) (i : Fin n) (s t : SourceSpinBasis (n+1)) :
    (qmaReferenceYEdge n i s t).im = 0 := by
  have hi : i.castSucc ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
  simp only [qmaReferenceYEdge,Matrix.smul_apply,smul_eq_mul,Complex.mul_im,
    Matrix.sub_apply,Complex.sub_im,sourcePauli_yy_real _ _ _ hi,Matrix.one_apply]
  split_ifs <;> norm_num

theorem qmaReferenceYEdge_hermitian (n : ℕ) (i : Fin n) :
    (qmaReferenceYEdge n i).IsHermitian := by
  apply qmaHermitian_of_conjugated (qmaReferenceTensor (n+1)) _
    (qmaReferenceTensor_cogram _)
  rw [qmaReferenceYEdge,qmaReferenceYEdge_diagonalized,sourceLocalPauli_z_diagonal,
    sourceLocalPauli_z_diagonal,Matrix.diagonal_mul_diagonal]
  apply Matrix.IsHermitian.ext
  intro s t
  by_cases h : s = t
  · subst t
    simp [Matrix.smul_apply,smul_eq_mul,qmaZSign]
    split_ifs <;> norm_num
  · simp [Matrix.smul_apply,smul_eq_mul,h,Ne.symm h]

def qmaReferenceEdgeOnQubits (n : ℕ) (i : Fin n) :
    Matrix (Fin (n+1) ⊕ ι → Fin 2) (Fin (n+1) ⊕ ι → Fin 2) ℂ :=
  qmaJoinMatrix (qmaReferenceYEdge n i) (ι := Fin (n+1)) (κ := ι) 1

def qmaReferenceEdgeSites (n : ℕ) (i : Fin n) : Finset (Fin (n+1) ⊕ ι) :=
  {Sum.inl i.castSucc,Sum.inl i.succ}

theorem qmaReferenceEdgeOnQubits_local (n : ℕ) (i : Fin n) :
    QMALocalOn (qmaReferenceEdgeSites (ι := ι) n i) (qmaReferenceEdgeOnQubits (ι := ι) n i) := by
  have h := (qmaReferenceYEdge_local n i).joinLeft (κ := ι)
  simpa only [qmaReferenceEdgeSites,qmaReferenceEdgeOnQubits,
    Finset.map_insert,Finset.map_singleton,Function.Embedding.inl_apply] using h

theorem qmaReferenceEdgeOnQubits_real (n : ℕ) (i : Fin n)
    (s t : Fin (n+1) ⊕ ι → Fin 2) : (qmaReferenceEdgeOnQubits n i s t).im = 0 := by
  change (qmaReferenceYEdge n i (s ∘ Sum.inl) (t ∘ Sum.inl)*
    (1 : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (s ∘ Sum.inr) (t ∘ Sum.inr)).im = 0
  simp only [Complex.mul_im,qmaReferenceYEdge_real,zero_mul,add_zero,Matrix.one_apply]
  split_ifs <;> simp

theorem qmaReferenceEdgeOnQubits_hermitian (n : ℕ) (i : Fin n) :
    (qmaReferenceEdgeOnQubits (ι := ι) n i).IsHermitian := by
  apply Matrix.IsHermitian.submatrix
  simp only [Matrix.IsHermitian,Matrix.conjTranspose_kronecker,
    (qmaReferenceYEdge_hermitian n i).eq,Matrix.conjTranspose_one]

end ContinuumCoulomb

end

end OAI
