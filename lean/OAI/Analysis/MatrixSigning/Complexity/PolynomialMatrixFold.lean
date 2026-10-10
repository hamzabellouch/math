import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialArrays
import OAI.Analysis.MatrixSigning.Realization.PencilArrayRealization

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

def QParts (H : ℕ) (q : ℚ) : Prop := q.num.natAbs≤2^H ∧ q.den≤2^H
lemma QParts.mono {H K : ℕ} {q : ℚ} (h : QParts H q) (hk : H≤K) : QParts K q :=
  ⟨h.1.trans (Nat.pow_le_pow_right (by decide) hk),h.2.trans (Nat.pow_le_pow_right (by decide) hk)⟩
lemma qparts_zero (H : ℕ) : QParts H 0 := by constructor <;> simp [Nat.one_le_two_pow]
lemma qparts_length (q : ℚ) : QParts (ratCode q).length q := KS.W01.rational_parts_le_two_pow_length q
lemma QParts.mul {H K : ℕ} {q r : ℚ} (hq : QParts H q) (hr : QParts K r) : QParts (H+K) (q*r) :=
  KS.W30.mul_parts_le_two_pow _ _ _ _ hq.1 hq.2 hr.1 hr.2
lemma QParts.add {H K : ℕ} {q r : ℚ} (hq : QParts H q) (hr : QParts K r) : QParts (H+K+1) (q+r) := by
  have ht := KS.W30.add_parts_le_two_pow _ _ _ _ hq.1 hq.2 hr.1 hr.2
  exact ⟨ht.1,ht.2.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩
lemma QParts.length {H : ℕ} {q : ℚ} (hq : QParts H q) : (ratCode q).length≤4*H+7 := by
  have h := KS.W01.ratLength_le_of_parts q H H hq.1 hq.2
  change KS.W01.ratLength q≤4*H+7
  omega

lemma getD_property {α : Type*} (P : α → Prop) (xs : List α) (a : α) (i : ℕ)
    (ha : P a) (hx : ∀x∈xs,P x) : P (xs.getD i a) := by
  by_cases h : i<xs.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hx _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ha
lemma zipDefault_property {α β γ : Type*} (P : α → Prop) (Q : β → Prop) (R : γ → Prop)
    (f : α×β → γ) (a : α) (b : β) (xs : List α) (ys : List β)
    (ha : P a) (hb : Q b) (hx : ∀x∈xs,P x) (hy : ∀y∈ys,Q y)
    (hf : ∀ x y,P x → Q y → R (f (x,y))) :
    ∀z∈zipDefault f a b (xs,ys),R z := by
  intro z hz
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hz
  exact hf _ _ (getD_property P xs a i ha hx) (getD_property Q ys b i hb hy)

def MatrixParts (H : ℕ) (M : MatrixData) : Prop := ∀row∈M,∀q∈row,QParts H q
lemma matrixParts_zero (H : ℕ) : MatrixParts H [] := by simp [MatrixParts]
lemma matrixParts_length (M : MatrixData) : MatrixParts (matrixCode M).length M := by
  intro row hr q hq
  exact (qparts_length q).mono ((mem_length_le_code row hq).trans (mem_length_le_code M hr))
lemma MatrixParts.mono {H K : ℕ} {M : MatrixData} (h : MatrixParts H M) (hk : H≤K) : MatrixParts K M :=
  fun row hr q hq => (h row hr q hq).mono hk

def MatrixShape (L : ℕ) (M : MatrixData) : Prop := M.length≤L ∧ ∀row∈M,row.length≤L
lemma matrixShape_length (M : MatrixData) : MatrixShape (matrixCode M).length M := by
  refine ⟨list_length_le_code _ _,?_⟩
  intro row hr
  exact (list_length_le_code _ _).trans (mem_length_le_code M hr)
lemma MatrixShape.mono {L K : ℕ} {M : MatrixData} (h : MatrixShape L M) (hk : L≤K) : MatrixShape K M :=
  ⟨h.1.trans hk,fun row hr => (h.2 row hr).trans hk⟩
lemma matrix_length_bound {H L : ℕ} {M : MatrixData} (hh : MatrixParts H M) (hs : MatrixShape L M) :
    (matrixCode M).length≤L*(2*(L*(2*(4*H+7)+1))+1) := by
  apply (listCode_length_bound M _ (fun row hr => ?_)).trans (Nat.mul_le_mul_right _ hs.1)
  exact (listCode_length_bound row _ (fun q hq => (hh row hr q hq).length)).trans (Nat.mul_le_mul_right _ (hs.2 row hr))

lemma accumMatrix_shape {L : ℕ} (A : MatrixData) (p : ℚ×MatrixData)
    (h : MatrixShape L A) : MatrixShape L (accumMatrix (A,p)) := by
  constructor
  · simpa only [accumMatrix,zipDefault,List.length_map,List.length_range] using h.1
  · intro row hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    simp only [zipDefault,List.length_map,List.length_range]
    exact getD_property (fun row : List ℚ => row.length≤L) A [] i (by simp) h.2
lemma accumMatrix_parts {H K : ℕ} (A : MatrixData) (p : ℚ×MatrixData)
    (ha : MatrixParts H A) (hq : QParts K p.1) (hb : MatrixParts K p.2) :
    MatrixParts (H+2*K+1) (accumMatrix (A,p)) := by
  have hs : MatrixParts (2*K) (p.2.map (fun row => row.map (fun x => p.1*x))) := by
    intro row hr0 q hq0
    obtain ⟨r,hr1,he⟩ := List.mem_map.mp hr0
    subst row
    obtain ⟨v,hv1,he'⟩ := List.mem_map.mp hq0
    subst q
    simpa [two_mul] using hq.mul (hb r hr1 v hv1)
  apply zipDefault_property
    (fun row => ∀q∈row,QParts H q) (fun row => ∀q∈row,QParts (2*K) q)
    (fun row => ∀q∈row,QParts (H+2*K+1) q) _ [] [] A _ (by simp) (by simp) ha hs
  intro x y hx hy
  exact zipDefault_property _ _ _ _ 0 0 x y (qparts_zero _) (qparts_zero _) hx hy (fun a b ha hb => ha.add hb)

lemma accumMatrix_fold {L H : ℕ} (A : MatrixData) (xs : List (ℚ×MatrixData))
    (shape : MatrixShape L A) (parts : MatrixParts H A)
    (hp : ∀p∈xs,QParts L p.1 ∧ MatrixParts L p.2) :
    MatrixShape L (xs.foldl (fun a p => accumMatrix (a,p)) A) ∧
      MatrixParts (H+xs.length*(2*L+1)) (xs.foldl (fun a p => accumMatrix (a,p)) A) := by
  induction xs generalizing A H with
  | nil => simpa using And.intro shape parts
  | cons x xs ih =>
    have h := ih (accumMatrix (A,x)) (accumMatrix_shape A x shape)
      (accumMatrix_parts A x parts (hp x (by simp)).1 (hp x (by simp)).2)
      (fun p hp' => hp p (by simp [hp']))
    simpa only [List.foldl_cons,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

instance poly_accumMatrix : PolyTime accumMatrixRealizes := by
  unfold accumMatrixRealizes
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_both
  · exact poly_matrixAdd
instance size_accumMatrix : FoldSize accumMatrixRealizes := by
  refine ⟨⟨1000*(X+1)^4,?_⟩⟩
  intro A xs ys zs h
  let L := (prodCode matrixCode (listCode (prodCode ratCode matrixCode)) (A,xs)).length
  have ha : (matrixCode A).length≤L := le_prodCode_left (A,xs)
  have hy : (listCode (prodCode ratCode matrixCode) ys).length≤L :=
    (prefix_code_length _ xs ys zs h).trans (le_prodCode_right (A,xs))
  have hn := (list_length_le_code _ _).trans hy
  have ht := accumMatrix_fold A ys ((matrixShape_length A).mono ha) ((matrixParts_length A).mono ha)
    (fun p hp => by
      have hl : (prodCode ratCode matrixCode p).length≤L := (mem_length_le_code ys hp).trans hy
      exact ⟨(qparts_length p.1).mono ((le_prodCode_left p).trans hl),
        (matrixParts_length p.2).mono ((le_prodCode_right p).trans hl)⟩)
  have he := matrix_length_bound ht.2 ht.1
  have he' : L+ys.length*(2*L+1)≤L+L*(2*L+1) := Nat.add_le_add_left (Nat.mul_le_mul_right _ hn) L
  apply he.trans
  change L*(2*(L*(2*(4*(L+ys.length*(2*L+1))+7)+1))+1)≤1000*(L+1)^4
  calc
    _≤ L*(2*(L*(2*(4*(L+L*(2*L+1))+7)+1))+1) := by gcongr
    _≤_ := by nlinarith [Nat.zero_le L, sq_nonneg (L:ℤ)]
instance poly_evalPencil : PolyTime evalPencil := by unfold evalPencil;apply poly_then
instance poly_normalPencil : PolyTime normalPencil := by unfold normalPencil;apply poly_then

end CurrentKS.Realization

end

end OAI
