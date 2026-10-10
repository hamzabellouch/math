import OAI.Analysis.Quantum.PPTSquare.PairResult

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace ChannelCompletion
variable {n p : Type} [Fintype n] [Fintype p]

def rename (e : p ≃ n) (F : Map n n) : Map p p where
  toFun A := (F (A.submatrix e.symm e.symm)).submatrix e e
  map_add' A B := by
    change (F (A.submatrix e.symm e.symm+B.submatrix e.symm e.symm)).submatrix e e=_
    rw [map_add]
    rfl
  map_smul' c A := by
    change (F (c • A.submatrix e.symm e.symm)).submatrix e e=_
    rw [map_smul]
    rfl
omit [Fintype n] [Fintype p] in
lemma rename_cp (e : p ≃ n) {F : Map n n} (hF : CP F) : CP (rename e F) := by
  intro k _ X hX
  exact (hF k (X.submatrix (Prod.map id e.symm) (Prod.map id e.symm))
    (hX.submatrix _)).submatrix (Prod.map id e)
omit [Fintype n] [Fintype p] in
lemma rename_transpose (e : p ≃ n) (F : Map n n) :
    rename e (transposeMap.comp F)=transposeMap.comp (rename e F) := by
  ext A i j
  rfl
omit [Fintype n] [Fintype p] in
lemma rename_ppt (e : p ≃ n) {F : Map n n} (hF : PPT F) : PPT (rename e F) := by
  refine ⟨rename_cp e hF.1,?_⟩
  rw [← rename_transpose]
  exact rename_cp e hF.2
lemma trace_submatrix_equivalence (e : p ≃ n) (A : Mat n) :
    Matrix.trace (A.submatrix e e)=Matrix.trace A := by
  exact e.sum_comp (fun i => A i i)
lemma rename_tracePreserving (e : p ≃ n) {F : Map n n} (hF : TracePreserving F) :
    TracePreserving (rename e F) := by
  intro A
  change Matrix.trace ((F (A.submatrix e.symm e.symm)).submatrix e e)=_
  rw [trace_submatrix_equivalence,hF,trace_submatrix_equivalence]
omit [Fintype n] [Fintype p] in
lemma rename_comp (e : p ≃ n) (G F : Map n n) :
    (rename e G).comp (rename e F)=rename e (G.comp F) := by
  ext A i j
  change G (((F (A.submatrix e.symm e.symm)).submatrix e e).submatrix e.symm e.symm) (e i) (e j)=_
  have h (B : Mat n) : (B.submatrix e e).submatrix e.symm e.symm=B := by
    ext a b
    simp only [Matrix.submatrix_apply,e.apply_symm_apply]
  rw [h]
  rfl
omit [Fintype n] [Fintype p] in
lemma eb_of_rename (e : p ≃ n) {F : Map n n} (hF : CP F)
    (h : EntanglementBreaking (rename e F)) : EntanglementBreaking F := by
  refine ⟨hF,?_⟩
  intro k _ X hX
  have hp := h.2 k (X.submatrix (Prod.map id e) (Prod.map id e)) (hX.submatrix _)
  have hs := separable_submatrix hp id e.symm
  convert hs using 1
  ext i j
  change F (fun a b => X (i.1,a) (j.1,b)) i.2 j.2=
    F (fun a b => X (i.1,e (e.symm a)) (j.1,e (e.symm b))) (e (e.symm i.2)) (e (e.symm j.2))
  simp only [e.apply_symm_apply]
end ChannelCompletion
namespace ExplicitPencil
open ChannelCompletion

def orderedCoordinates : Space 10 ≃ Fin 21 :=
  (Equiv.sumCongr (finSumFinEquiv : (Fin 10 ⊕ Fin 10) ≃ Fin 20)
    (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv
lemma orderedCoordinates_first (i : Fin 10) :
    (orderedCoordinates (first 10 i)).val=i.val := rfl
lemma orderedCoordinates_second (i : Fin 10) :
    (orderedCoordinates (second 10 i)).val=10+i.val := rfl
lemma orderedCoordinates_flag : (orderedCoordinates (flag 10)).val=20 := rfl

def Theta21 : Map (Fin 21) (Fin 21) := rename orderedCoordinates.symm Theta

theorem main_channel_fin21 : PPT Theta21 ∧ TracePreserving Theta21 ∧
    ¬ EntanglementBreaking (Theta21.comp Theta21) := by
  obtain ⟨hd,hP,hT,hE⟩ := main_channel
  refine ⟨rename_ppt _ hP,rename_tracePreserving _ hT,?_⟩
  intro hn
  unfold Theta21 at hn
  rw [rename_comp] at hn
  exact hE (eb_of_rename _ (cp_comp hP.1 hP.1) hn)
end ExplicitPencil

end

end OAI
