import Mathlib

namespace OAI

section
namespace ElementaryPositivity.ElementaryMatrix
open scoped BigOperators
open Classical
noncomputable section
variable {A B:Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def transpose (s:B → Finset A) : A → Finset B:=fun a=>Finset.univ.filter (fun b=>a∈s b)
lemma transpose_transpose (s:B → Finset A) : transpose (transpose s)=s := by
  funext b
  ext a
  simp [transpose]
def transposeEquiv : (B → Finset A) ≃ (A → Finset B) where
  toFun:=transpose
  invFun:=transpose
  left_inv:=transpose_transpose
  right_inv:=transpose_transpose

def rowCount (s:B → Finset A) : B →₀ ℕ:=Finsupp.equivFunOnFinite.symm (fun b=>(s b).card)
def colCount (s:B → Finset A) : A →₀ ℕ:=∑b,∑a∈s b,Finsupp.single a 1
omit [Fintype A] [DecidableEq B] in
lemma colCount_apply (s:B → Finset A) (a:A) : colCount s a=(transpose s a).card := by
  simp only [colCount,Finsupp.finsetSum_apply,Finsupp.single_apply]
  simp only [Finset.sum_ite_eq',Finset.sum_boole]
  rfl
omit [DecidableEq B] in
lemma rowCount_transpose (s:B → Finset A) : rowCount (transpose s)=colCount s := by
  ext a
  exact (colCount_apply s a).symm
lemma colCount_transpose (s:B → Finset A) : colCount (transpose s)=rowCount s := by
  rw [←rowCount_transpose,transpose_transpose]
omit [Fintype A] [DecidableEq A] [DecidableEq B] in
lemma rowCount_eq (s:B → Finset A) (a:B →₀ ℕ) : rowCount s=a ↔ ∀b,(s b).card=a b := by
  exact Finsupp.ext_iff

variable {R:Type*} [CommSemiring R]
omit [DecidableEq A] in
lemma esymm_all (k:ℕ) : MvPolynomial.esymm A R k=
    ∑s:Finset A,if s.card=k then MvPolynomial.monomial (∑a∈s,Finsupp.single a 1) (1:R) else 0 := by
  rw [MvPolynomial.esymm_eq_sum_monomial]
  have H:Finset.powersetCard k (Finset.univ:Finset A)=Finset.univ.filter (fun s:Finset A=>s.card=k):=by
    ext s
    simp
  rw [H,Finset.sum_filter]

omit [DecidableEq A] in
lemma elementary_product (a:B →₀ ℕ) :
    (∏b: B,MvPolynomial.esymm A R (a b))=
      ∑s:B → Finset A,if rowCount s=a then MvPolynomial.monomial (colCount s) (1:R) else 0 := by
  simp only [esymm_all]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h:rowCount s=a
  · rw [ite_eq_left h]
    have h':∀b,(s b).card=a b:=(rowCount_eq s a).mp h
    simp only [h',ite_true]
    exact (MvPolynomial.monomial_sum_one Finset.univ (fun b=>∑a∈s b,Finsupp.single a 1)).symm
  · rw [ite_eq_right h]
    obtain ⟨b,hb⟩:=not_forall.mp (mt (rowCount_eq s a).mpr h)
    exact Finset.prod_eq_zero (Finset.mem_univ b) (ite_eq_right hb)

lemma elementary_product_coeff (a:B →₀ ℕ) (μ:A →₀ ℕ) :
    (∏b:B,MvPolynomial.esymm A R (a b)).coeff μ=
      ∑s:B → Finset A,if rowCount s=a ∧ colCount s=μ then (1:R) else 0 := by
  rw [elementary_product,MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h:rowCount s=a
  · simp only [h,ite_true,true_and,MvPolynomial.coeff_monomial]
  · simp only [h,ite_false,false_and,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]

theorem duality (a:B →₀ ℕ) (μ:A →₀ ℕ) :
    (∏b:B,MvPolynomial.esymm A R (a b)).coeff μ=
      (∏i:A,MvPolynomial.esymm B R (μ i)).coeff a := by
  rw [elementary_product_coeff,elementary_product_coeff,
    ←Equiv.sum_comp (transposeEquiv (A:=A) (B:=B))]
  apply Finset.sum_congr rfl
  intro s hs
  change (if rowCount s=a ∧ colCount s=μ then (1:R) else 0)=
    if rowCount (transpose s)=μ ∧ colCount (transpose s)=a then 1 else 0
  simp only [rowCount_transpose,colCount_transpose,and_comm]
end
end ElementaryPositivity.ElementaryMatrix

end

end OAI
