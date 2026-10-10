import OAI.InformationTheory.Entanglement.SecretDefinitions

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {a b c d r s u v : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
  [Fintype r] [Fintype s] [Fintype u] [Fintype v]

def groupedTensor (A : Mat (a × b)) (B : Mat (c × d)) : Mat ((a × c) × (b × d)) :=
  (A ⊗ₖ B).submatrix (Equiv.prodProdProdComm a c b d) (Equiv.prodProdProdComm a c b d)

omit [Fintype a] [Fintype b] [Fintype c] [Fintype d] in
lemma groupedTensor_apply (A : Mat (a × b)) (B : Mat (c × d))
    (i j : (a × c) × (b × d)) :
    groupedTensor A B i j=A (i.1.1,i.2.1) (j.1.1,j.2.1)*B (i.1.2,i.2.2) (j.1.2,j.2.2) := rfl

lemma groupedTensor_psd {A : Mat (a × b)} {B : Mat (c × d)}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (groupedTensor A B).PosSemidef :=
  (hA.kronecker hB).submatrix _

lemma groupedTensor_trace (A : Mat (a × b)) (B : Mat (c × d)) :
    Matrix.trace (groupedTensor A B)=Matrix.trace A*Matrix.trace B := by
  change (∑ i, (A ⊗ₖ B) ((Equiv.prodProdProdComm a c b d) i) ((Equiv.prodProdProdComm a c b d) i))=_
  exact ((Equiv.prodProdProdComm a c b d).sum_comp
    (fun i => (A ⊗ₖ B) i i)).trans (Matrix.trace_kronecker A B)

lemma tensorMap_input_transpose (F : Map a b) (G : Map c d) :
    (tensorMap F G).comp transposeMap=tensorMap (F.comp transposeMap) (G.comp transposeMap) := rfl

def inputReindex (e : r ≃ a) (F : Map a b) : Map r b where
  toFun A := F (A.submatrix e.symm e.symm)
  map_add' A B := by exact map_add F _ _
  map_smul' z A := by exact map_smul F _ _

omit [Fintype a] [Fintype b] [Fintype r] in
lemma inputReindex_cp (e : r ≃ a) {F : Map a b} (hF : CP F) : CP (inputReindex e F) := by
  intro k _ X hX
  exact hF k (X.submatrix (Prod.map id e.symm) (Prod.map id e.symm)) (hX.submatrix _)

omit [Fintype a] [Fintype b] [Fintype r] in
lemma inputReindex_transpose (e : r ≃ a) (F : Map a b) :
    (inputReindex e F).comp transposeMap=inputReindex e (F.comp transposeMap) := rfl

lemma tensorMap_inputReindex (e : r ≃ a) (f : s ≃ c) (F : Map a b) (G : Map c d)
    (A : Mat (r × s)) :
    tensorMap (inputReindex e F) (inputReindex f G) A=
      tensorMap F G (A.submatrix (e.symm.prodCongr f.symm) (e.symm.prodCongr f.symm)) := rfl

lemma represented_of_finite [Nonempty r] [Nonempty s]
    {R : Mat (a × b)} (hR : R.PosSemidef) (ht : Matrix.trace R=1)
    (L : Map r a) (M : Map s b) (χ : r × s → ℂ)
    (hL : CP L) (hLT : CP (L.comp transposeMap))
    (hM : CP M) (hMT : CP (M.comp transposeMap))
    (he : R=tensorMap L M (projector χ)) : Represented R := by
  classical
  let e := (Fintype.equivFin r).symm
  let f := (Fintype.equivFin s).symm
  refine ⟨hR,ht,Fintype.card r,Fintype.card s,Fintype.card_pos,Fintype.card_pos,
    inputReindex e L,inputReindex f M,χ ∘ (e.prodCongr f),inputReindex_cp e hL,?_,
    inputReindex_cp f hM,?_,?_⟩
  · rw [inputReindex_transpose]
    exact inputReindex_cp e hLT
  · rw [inputReindex_transpose]
    exact inputReindex_cp f hMT
  · rw [tensorMap_inputReindex]
    convert he using 1
    congr 1
    ext ⟨i,i'⟩ ⟨j,j'⟩
    simp only [projector,Matrix.submatrix_apply,Matrix.vecMulVec_apply,Pi.star_apply,
      Function.comp_apply,Equiv.prodCongr_apply,Prod.map_apply,Equiv.apply_symm_apply]

omit [Fintype a] [Fintype b] [Fintype c] [Fintype d] in
lemma groupedTensor_projector (χ : a × b → ℂ) (ψ : c × d → ℂ) :
    groupedTensor (projector χ) (projector ψ)=
      projector (fun i : (a × c) × (b × d) => χ (i.1.1,i.2.1)*ψ (i.1.2,i.2.2)) := by
  ext i j
  simp only [groupedTensor_apply,projector,Matrix.vecMulVec_apply,Pi.star_apply,star_mul]
  ring
lemma tensorMap_groupedTensor (L : Map r a) (M : Map s b)
    (L' : Map u c) (M' : Map v d) (A : Mat (r × s)) (B : Mat (u × v)) :
    tensorMap (tensorMap L L') (tensorMap M M') (groupedTensor A B)=
      groupedTensor (tensorMap L M A) (tensorMap L' M' B) := by
  ext i j
  change tensorMap L L' (Matrix.of fun k l =>
    tensorMap M M' ((Matrix.of fun x y => A (k.1,x) (l.1,y)) ⊗ₖ
      (Matrix.of fun x y => B (k.2,x) (l.2,y))) i.2 j.2) i.1 j.1=_
  simp_rw [tensorMap_kronecker]
  change tensorMap L L' ((Matrix.of fun k l => M (Matrix.of fun x y => A (k,x) (l,y)) i.2.1 j.2.1) ⊗ₖ
    (Matrix.of fun k l => M' (Matrix.of fun x y => B (k,x) (l,y)) i.2.2 j.2.2)) i.1 j.1=_
  rw [tensorMap_kronecker]
  rfl

theorem represented_groupedTensor {A : Mat (a × b)} {B : Mat (c × d)}
    (hA : Represented A) (hB : Represented B) : Represented (groupedTensor A B) := by
  classical
  obtain ⟨hAp,hAt,r,s,hr,hs,L,M,χ,hL,hLT,hM,hMT,hA⟩ := hA
  obtain ⟨hBp,hBt,u,v,hu,hv,L',M',ψ,hL',hLT',hM',hMT',hB⟩ := hB
  let : NeZero r := ⟨Nat.ne_of_gt hr⟩
  let : NeZero s := ⟨Nat.ne_of_gt hs⟩
  let : NeZero u := ⟨Nat.ne_of_gt hu⟩
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  refine represented_of_finite (groupedTensor_psd hAp hBp)
    (by rw [groupedTensor_trace,hAt,hBt]; ring)
    (tensorMap L L') (tensorMap M M')
    (fun i => χ (i.1.1,i.2.1)*ψ (i.1.2,i.2.2))
    (cp_tensorMap hL hL') ?_ (cp_tensorMap hM hM') ?_ ?_
  · rw [tensorMap_input_transpose]
    exact cp_tensorMap hLT hLT'
  · rw [tensorMap_input_transpose]
    exact cp_tensorMap hMT hMT'
  · rw [← groupedTensor_projector,tensorMap_groupedTensor]
    exact congrArg₂ groupedTensor hA hB

def CopyIndex (a : Type) : ℕ → Type
  | 0 => a
  | k+1 => CopyIndex a k × a

instance copyIndex_fintype (a : Type) [Fintype a] : (k : ℕ) → Fintype (CopyIndex a k)
  | 0 => inferInstanceAs (Fintype a)
  | k+1 => letI := copyIndex_fintype a k; inferInstanceAs (Fintype (CopyIndex a k × a))

def groupedCopies (A : Mat (a × b)) : (k : ℕ) → Mat (CopyIndex a k × CopyIndex b k)
  | 0 => A
  | k+1 => groupedTensor (groupedCopies A k) A

lemma copyIndex_card (a : Type) [Fintype a] (k : ℕ) :
    Fintype.card (CopyIndex a k)=Fintype.card a^(k+1) := by
  induction k with
  | zero => change Fintype.card a=Fintype.card a^1; simp
  | succ k ih =>
    change Fintype.card (CopyIndex a k × a)=_
    rw [Fintype.card_prod,ih]
    exact (pow_succ (Fintype.card a) (k+1)).symm

theorem represented_groupedCopies {A : Mat (a × b)} (hA : Represented A) (k : ℕ) :
    Represented (groupedCopies A k) := by
  induction k with
  | zero => exact hA
  | succ k ih => exact represented_groupedTensor ih hA

end SecretKey

end

end OAI
