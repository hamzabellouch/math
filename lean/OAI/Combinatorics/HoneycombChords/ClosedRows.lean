import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Ring

namespace OAI

/-! Four-row transfer identities and boundary contractions.

This development follows the finite strip transfer calculation for critical honeycomb
walks in the companion paper on uniform marked polygon estimates. -/

section

namespace CriticalHoneycomb.Transfer.ClosedFourRow
open scoped Matrix BigOperators

section Algebra
variable {R : Type*} [Monoid R]
lemma middle_exchange (A B C D E : R) (hA : Commute E A) (hD : Commute E D)
    (h : E*(B*C)=(C*B)*E) : E*(A*B*C*D)=(A*C*B*D)*E := by
  calc
    _ = (E*A)*(B*C)*D := by simp only [mul_assoc]
    _ = (A*E)*(B*C)*D := by rw [hA.eq]
    _ = A*(E*(B*C))*D := by simp only [mul_assoc]
    _ = A*((C*B)*E)*D := by rw [h]
    _ = (A*C*B)*(E*D) := by simp only [mul_assoc]
    _ = (A*C*B)*(D*E) := by rw [hD.eq]
    _ = _ := by simp only [mul_assoc]
lemma first_exchange (A B C D E : R) (hC : Commute E C) (hD : Commute E D)
    (h : E*(A*B)=(B*A)*E) : E*(A*B*C*D)=(B*A*C*D)*E := by
  calc
    _ = (E*(A*B))*C*D := by simp only [mul_assoc]
    _ = ((B*A)*E)*C*D := by rw [h]
    _ = (B*A)*(E*C)*D := by simp only [mul_assoc]
    _ = (B*A)*(C*E)*D := by rw [hC.eq]
    _ = (B*A*C)*(E*D) := by simp only [mul_assoc]
    _ = (B*A*C)*(D*E) := by rw [hD.eq]
    _ = _ := by simp only [mul_assoc]
lemma last_exchange (A B C D E : R) (hA : Commute E A) (hB : Commute E B)
    (h : E*(C*D)=(D*C)*E) : E*(A*B*C*D)=(A*B*D*C)*E := by
  calc
    _ = (E*A)*(B*(C*D)) := by simp only [mul_assoc]
    _ = (A*E)*(B*(C*D)) := by rw [hA.eq]
    _ = A*(E*B)*(C*D) := by simp only [mul_assoc]
    _ = A*(B*E)*(C*D) := by rw [hB.eq]
    _ = (A*B)*(E*(C*D)) := by simp only [mul_assoc]
    _ = (A*B)*((D*C)*E) := by rw [h]
    _ = _ := by simp only [mul_assoc]

theorem four_train (A B C D E₁ E₂ E₃ E₄ : R)
    (h₁ : E₁*(A*B*C*D)=(A*C*B*D)*E₁)
    (h₂ : E₂*(A*C*B*D)=(C*A*B*D)*E₂)
    (h₃ : E₃*(C*A*B*D)=(C*A*D*B)*E₃)
    (h₄ : E₄*(C*A*D*B)=(C*D*A*B)*E₄) :
    (E₄*E₃*E₂*E₁)*(A*B*C*D)=(C*D*A*B)*(E₄*E₃*E₂*E₁) := by
  calc
    _ = (E₄*E₃*E₂)*(E₁*(A*B*C*D)) := by simp only [mul_assoc]
    _ = (E₄*E₃*E₂)*((A*C*B*D)*E₁) := by rw [h₁]
    _ = (E₄*E₃)*(E₂*(A*C*B*D))*E₁ := by simp only [mul_assoc]
    _ = (E₄*E₃)*((C*A*B*D)*E₂)*E₁ := by rw [h₂]
    _ = E₄*(E₃*(C*A*B*D))*E₂*E₁ := by simp only [mul_assoc]
    _ = E₄*((C*A*D*B)*E₃)*E₂*E₁ := by rw [h₃]
    _ = (E₄*(C*A*D*B))*E₃*E₂*E₁ := by simp only [mul_assoc]
    _ = ((C*D*A*B)*E₄)*E₃*E₂*E₁ := by rw [h₄]
    _ = _ := by simp only [mul_assoc]
end Algebra

section Lift
variable {α ι k : Type*} [CommSemiring k] [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]
abbrev Aux (α : Type*) := α × α × α × α
abbrev AuxSite (α ι : Type*) := Aux α × ι
abbrev Row (α ι k : Type*) := ι → ι → Matrix α α k
abbrev Total (α ι k : Type*) := Matrix (AuxSite α ι) (AuxSite α ι) k
noncomputable def rowA (M : Row α ι k) : Total α ι k := fun p q =>
  M p.2 q.2 p.1.1 q.1.1 *
    (1 : Matrix α α k) p.1.2.1 q.1.2.1 * (1 : Matrix α α k) p.1.2.2.1 q.1.2.2.1 *
      (1 : Matrix α α k) p.1.2.2.2 q.1.2.2.2
noncomputable def rowB (M : Row α ι k) : Total α ι k := fun p q =>
  M p.2 q.2 p.1.2.1 q.1.2.1 *
    (1 : Matrix α α k) p.1.1 q.1.1 * (1 : Matrix α α k) p.1.2.2.1 q.1.2.2.1 *
      (1 : Matrix α α k) p.1.2.2.2 q.1.2.2.2
noncomputable def rowC (M : Row α ι k) : Total α ι k := fun p q =>
  M p.2 q.2 p.1.2.2.1 q.1.2.2.1 *
    (1 : Matrix α α k) p.1.1 q.1.1 * (1 : Matrix α α k) p.1.2.1 q.1.2.1 *
      (1 : Matrix α α k) p.1.2.2.2 q.1.2.2.2
noncomputable def rowD (M : Row α ι k) : Total α ι k := fun p q =>
  M p.2 q.2 p.1.2.2.2 q.1.2.2.2 *
    (1 : Matrix α α k) p.1.1 q.1.1 * (1 : Matrix α α k) p.1.2.1 q.1.2.1 *
      (1 : Matrix α α k) p.1.2.2.1 q.1.2.2.1
noncomputable def exBC (F : Matrix (α×α) (α×α) k) : Total α ι k := fun p q =>
  F (p.1.2.1,p.1.2.2.1) (q.1.2.1,q.1.2.2.1) *
    (1 : Matrix α α k) p.1.1 q.1.1 * (1 : Matrix α α k) p.1.2.2.2 q.1.2.2.2 *
      (1 : Matrix ι ι k) p.2 q.2
lemma exBC_rowA (F : Matrix (α×α) (α×α) k) (M : Row α ι k) :
    Commute (exBC F) (rowA M) := by
  change exBC F * rowA M = rowA M * exBC F
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exBC,rowA,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
  split_ifs <;> ring
lemma exBC_rowD (F : Matrix (α×α) (α×α) k) (M : Row α ι k) :
    Commute (exBC F) (rowD M) := by
  change exBC F * rowD M = rowD M * exBC F
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exBC,rowD,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
  split_ifs <;> ring
noncomputable def exAC (F : Matrix (α×α) (α×α) k) : Total α ι k := fun p q =>
  F (p.1.1,p.1.2.2.1) (q.1.1,q.1.2.2.1) *
    (1 : Matrix α α k) p.1.2.1 q.1.2.1 *
      (1 : Matrix α α k) p.1.2.2.2 q.1.2.2.2 *
        (1 : Matrix ι ι k) p.2 q.2
lemma exAC_rowB (F : Matrix (α×α) (α×α) k) (M : Row α ι k) :
    Commute (exAC F) (rowB M) := by
  change exAC F * rowB M = rowB M * exAC F
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exAC,rowB,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
  split_ifs <;> ring
lemma exAC_rowD (F : Matrix (α×α) (α×α) k) (M : Row α ι k) :
    Commute (exAC F) (rowD M) := by
  change exAC F * rowD M = rowD M * exAC F
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exAC,rowD,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
  split_ifs <;> ring
noncomputable def exBD (F : Matrix (α×α) (α×α) k) : Total α ι k := fun p q =>
  F (p.1.2.1,p.1.2.2.2) (q.1.2.1,q.1.2.2.2) *
    (1 : Matrix α α k) p.1.1 q.1.1 *
      (1 : Matrix α α k) p.1.2.2.1 q.1.2.2.1 *
        (1 : Matrix ι ι k) p.2 q.2
lemma exBD_rowA (F : Matrix (α×α) (α×α) k) (M : Row α ι k) :
    Commute (exBD F) (rowA M) := by
  change exBD F * rowA M = rowA M * exBD F
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exBD,rowA,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
  split_ifs <;> ring
lemma exBD_rowC (F : Matrix (α×α) (α×α) k) (M : Row α ι k) :
    Commute (exBD F) (rowC M) := by
  change exBD F * rowC M = rowC M * exBD F
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exBD,rowC,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
  split_ifs <;> ring
noncomputable def exAD (F : Matrix (α×α) (α×α) k) : Total α ι k := fun p q =>
  F (p.1.1,p.1.2.2.2) (q.1.1,q.1.2.2.2) *
    (1 : Matrix α α k) p.1.2.1 q.1.2.1 *
      (1 : Matrix α α k) p.1.2.2.1 q.1.2.2.1 *
        (1 : Matrix ι ι k) p.2 q.2
lemma exAD_rowB (F : Matrix (α×α) (α×α) k) (M : Row α ι k) :
    Commute (exAD F) (rowB M) := by
  change exAD F * rowB M = rowB M * exAD F
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exAD,rowB,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
  split_ifs <;> ring
lemma exAD_rowC (F : Matrix (α×α) (α×α) k) (M : Row α ι k) :
    Commute (exAD F) (rowC M) := by
  change exAD F * rowC M = rowC M * exAD F
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exAD,rowC,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
  split_ifs <;> ring
noncomputable def forwardPair (M N : Row α ι k) (s t : ι) : Matrix (α×α) (α×α) k :=
  ∑ v, Matrix.kronecker (M s v) (N v t)
noncomputable def backwardPair (M N : Row α ι k) (s t : ι) : Matrix (α×α) (α×α) k :=
  ∑ v, Matrix.kronecker (M v t) (N s v)
noncomputable def pairBC (P : ι → ι → Matrix (α×α) (α×α) k) : Total α ι k := fun p q =>
  P p.2 q.2 (p.1.2.1,p.1.2.2.1) (q.1.2.1,q.1.2.2.1) *
    (1 : Matrix α α k) p.1.1 q.1.1 *
      (1 : Matrix α α k) p.1.2.2.2 q.1.2.2.2
omit [DecidableEq ι] in
lemma pairBC_forward (M N : Row α ι k) :
    rowB M * rowC N = pairBC (forwardPair M N) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [rowB,rowC,pairBC,forwardPair,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap,Matrix.one_apply,mul_ite,ite_mul,
    Matrix.sum_apply,Matrix.of_apply]
omit [DecidableEq ι] in
lemma pairBC_backward (M N : Row α ι k) :
    rowC N * rowB M = pairBC (backwardPair M N) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [rowB,rowC,pairBC,backwardPair,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap,Matrix.one_apply,mul_ite,ite_mul,
    Matrix.sum_apply,Matrix.of_apply]
  split_ifs <;> simp_all [mul_comm]
lemma exBC_left (F : Matrix (α×α) (α×α) k)
    (P : ι → ι → Matrix (α×α) (α×α) k) :
    exBC F * pairBC P = pairBC (fun s t => F * P s t) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exBC,pairBC,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
lemma exBC_right (F : Matrix (α×α) (α×α) k)
    (P : ι → ι → Matrix (α×α) (α×α) k) :
    pairBC P * exBC F = pairBC (fun s t => P s t * F) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exBC,pairBC,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
lemma exchangeBC (F : Matrix (α×α) (α×α) k) (M N : Row α ι k)
    (h : ∀ s t, F * forwardPair M N s t = backwardPair M N s t * F) :
    exBC F * (rowB M * rowC N) = (rowC N * rowB M) * exBC F := by
  rw [pairBC_forward,pairBC_backward,exBC_left,exBC_right]
  congr 1
  funext s t
  exact h s t
noncomputable def pairAC (P : ι → ι → Matrix (α×α) (α×α) k) : Total α ι k := fun p q =>
  P p.2 q.2 (p.1.1,p.1.2.2.1) (q.1.1,q.1.2.2.1) *
    (1 : Matrix α α k) p.1.2.1 q.1.2.1 *
      (1 : Matrix α α k) p.1.2.2.2 q.1.2.2.2
omit [DecidableEq ι] in
lemma pairAC_forward (M N : Row α ι k) :
    rowA M * rowC N = pairAC (forwardPair M N) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [rowA,rowC,pairAC,forwardPair,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap,Matrix.one_apply,mul_ite,ite_mul,
    Matrix.sum_apply,Matrix.of_apply]
omit [DecidableEq ι] in
lemma pairAC_backward (M N : Row α ι k) :
    rowC N * rowA M = pairAC (backwardPair M N) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [rowA,rowC,pairAC,backwardPair,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap,Matrix.one_apply,mul_ite,ite_mul,
    Matrix.sum_apply,Matrix.of_apply]
  split_ifs <;> simp_all [mul_comm]
lemma exAC_left (F : Matrix (α×α) (α×α) k)
    (P : ι → ι → Matrix (α×α) (α×α) k) :
    exAC F * pairAC P = pairAC (fun s t => F * P s t) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exAC,pairAC,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
lemma exAC_right (F : Matrix (α×α) (α×α) k)
    (P : ι → ι → Matrix (α×α) (α×α) k) :
    pairAC P * exAC F = pairAC (fun s t => P s t * F) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exAC,pairAC,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
lemma exchangeAC (F : Matrix (α×α) (α×α) k) (M N : Row α ι k)
    (h : ∀ s t, F * forwardPair M N s t = backwardPair M N s t * F) :
    exAC F * (rowA M * rowC N) = (rowC N * rowA M) * exAC F := by
  rw [pairAC_forward,pairAC_backward,exAC_left,exAC_right]
  congr 1
  funext s t
  exact h s t
noncomputable def pairBD (P : ι → ι → Matrix (α×α) (α×α) k) : Total α ι k := fun p q =>
  P p.2 q.2 (p.1.2.1,p.1.2.2.2) (q.1.2.1,q.1.2.2.2) *
    (1 : Matrix α α k) p.1.1 q.1.1 *
      (1 : Matrix α α k) p.1.2.2.1 q.1.2.2.1
omit [DecidableEq ι] in
lemma pairBD_forward (M N : Row α ι k) :
    rowB M * rowD N = pairBD (forwardPair M N) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [rowB,rowD,pairBD,forwardPair,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap,Matrix.one_apply,mul_ite,ite_mul,
    Matrix.sum_apply,Matrix.of_apply]
omit [DecidableEq ι] in
lemma pairBD_backward (M N : Row α ι k) :
    rowD N * rowB M = pairBD (backwardPair M N) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [rowB,rowD,pairBD,backwardPair,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap,Matrix.one_apply,mul_ite,ite_mul,
    Matrix.sum_apply,Matrix.of_apply]
  split_ifs <;> simp_all [mul_comm]
lemma exBD_left (F : Matrix (α×α) (α×α) k)
    (P : ι → ι → Matrix (α×α) (α×α) k) :
    exBD F * pairBD P = pairBD (fun s t => F * P s t) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exBD,pairBD,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
lemma exBD_right (F : Matrix (α×α) (α×α) k)
    (P : ι → ι → Matrix (α×α) (α×α) k) :
    pairBD P * exBD F = pairBD (fun s t => P s t * F) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exBD,pairBD,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
lemma exchangeBD (F : Matrix (α×α) (α×α) k) (M N : Row α ι k)
    (h : ∀ s t, F * forwardPair M N s t = backwardPair M N s t * F) :
    exBD F * (rowB M * rowD N) = (rowD N * rowB M) * exBD F := by
  rw [pairBD_forward,pairBD_backward,exBD_left,exBD_right]
  congr 1
  funext s t
  exact h s t
noncomputable def pairAD (P : ι → ι → Matrix (α×α) (α×α) k) : Total α ι k := fun p q =>
  P p.2 q.2 (p.1.1,p.1.2.2.2) (q.1.1,q.1.2.2.2) *
    (1 : Matrix α α k) p.1.2.1 q.1.2.1 *
      (1 : Matrix α α k) p.1.2.2.1 q.1.2.2.1
omit [DecidableEq ι] in
lemma pairAD_forward (M N : Row α ι k) :
    rowA M * rowD N = pairAD (forwardPair M N) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [rowA,rowD,pairAD,forwardPair,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap,Matrix.one_apply,mul_ite,ite_mul,
    Matrix.sum_apply,Matrix.of_apply]
omit [DecidableEq ι] in
lemma pairAD_backward (M N : Row α ι k) :
    rowD N * rowA M = pairAD (backwardPair M N) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [rowA,rowD,pairAD,backwardPair,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap,Matrix.one_apply,mul_ite,ite_mul,
    Matrix.sum_apply,Matrix.of_apply]
  split_ifs <;> simp_all [mul_comm]
lemma exAD_left (F : Matrix (α×α) (α×α) k)
    (P : ι → ι → Matrix (α×α) (α×α) k) :
    exAD F * pairAD P = pairAD (fun s t => F * P s t) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exAD,pairAD,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
lemma exAD_right (F : Matrix (α×α) (α×α) k)
    (P : ι → ι → Matrix (α×α) (α×α) k) :
    pairAD P * exAD F = pairAD (fun s t => P s t * F) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [exAD,pairAD,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
lemma exchangeAD (F : Matrix (α×α) (α×α) k) (M N : Row α ι k)
    (h : ∀ s t, F * forwardPair M N s t = backwardPair M N s t * F) :
    exAD F * (rowA M * rowD N) = (rowD N * rowA M) * exAD F := by
  rw [pairAD_forward,pairAD_backward,exAD_left,exAD_right]
  congr 1
  funext s t
  exact h s t

theorem lifted_four_train (A B C D : Row α ι k)
    (F₁ F₂ F₃ F₄ : Matrix (α×α) (α×α) k)
    (h₁ : ∀ s t, F₁ * forwardPair B C s t = backwardPair B C s t * F₁)
    (h₂ : ∀ s t, F₂ * forwardPair A C s t = backwardPair A C s t * F₂)
    (h₃ : ∀ s t, F₃ * forwardPair B D s t = backwardPair B D s t * F₃)
    (h₄ : ∀ s t, F₄ * forwardPair A D s t = backwardPair A D s t * F₄) :
    (exAD F₄ * exBD F₃ * exAC F₂ * exBC F₁) *
      (rowA A * rowB B * rowC C * rowD D) =
    (rowC C * rowD D * rowA A * rowB B) *
      (exAD F₄ * exBD F₃ * exAC F₂ * exBC F₁) := by
  apply four_train
  · exact middle_exchange _ _ _ _ _ (exBC_rowA F₁ A) (exBC_rowD F₁ D)
      (exchangeBC F₁ B C h₁)
  · exact first_exchange _ _ _ _ _ (exAC_rowB F₂ B) (exAC_rowD F₂ D)
      (exchangeAC F₂ A C h₂)
  · exact last_exchange _ _ _ _ _ (exBD_rowC F₃ C) (exBD_rowA F₃ A)
      (exchangeBD F₃ B D h₃)
  · exact middle_exchange _ _ _ _ _ (exAD_rowC F₄ C) (exAD_rowB F₄ B)
      (exchangeAD F₄ A D h₄)
end Lift
end CriticalHoneycomb.Transfer.ClosedFourRow

end

section

namespace CriticalHoneycomb.Transfer.ClosedFourRow
open scoped Matrix BigOperators

attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
section
variable {α ι k : Type*} [CommSemiring k] [Fintype α] [DecidableEq α]
  [Fintype ι] [DecidableEq ι]
noncomputable def auxLift (U : Matrix (Aux α) (Aux α) k) : Total α ι k := Matrix.kronecker U 1
noncomputable def leftWall (l : Aux α → k) : Matrix ι (AuxSite α ι) k :=
  fun s p => l p.1 * (1 : Matrix ι ι k) s p.2
noncomputable def rightWall (r : Aux α → k) : Matrix (AuxSite α ι) ι k :=
  fun p t => r p.1 * (1 : Matrix ι ι k) p.2 t
omit [DecidableEq α] in
lemma auxLift_mul (U V : Matrix (Aux α) (Aux α) k) :
    (auxLift (U*V) : Total α ι k) = auxLift U * auxLift V := by
  simpa only [auxLift,Matrix.kronecker,one_mul] using
    Matrix.mul_kronecker_mul U V (1 : Matrix ι ι k) (1 : Matrix ι ι k)
omit [DecidableEq α] in
lemma auxLift_rightWall (U : Matrix (Aux α) (Aux α) k) (r : Aux α → k) :
    (auxLift U : Total α ι k) * rightWall r = rightWall (U *ᵥ r) := by
  ext ⟨a,s⟩ t
  simp [auxLift,rightWall,Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap,
    Matrix.one_apply,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,mul_ite,ite_mul]
omit [DecidableEq α] in
lemma leftWall_auxLift (U : Matrix (Aux α) (Aux α) k) (l : Aux α → k) :
    (leftWall l : Matrix ι (AuxSite α ι) k) * auxLift U = leftWall (l ᵥ* U) := by
  ext s ⟨a,t⟩
  simp [auxLift,leftWall,Matrix.mul_apply,Matrix.kronecker,Matrix.kroneckerMap,
    Matrix.one_apply,Matrix.vecMul,dotProduct,Fintype.sum_prod_type,mul_ite,ite_mul]
noncomputable def close4 (l r : Aux α → k) (X : Total α ι k) : Matrix ι ι k :=
  leftWall l * X * rightWall r

omit [DecidableEq α] in
lemma close_train (U : Matrix (Aux α) (Aux α) k) (X Y : Total α ι k)
    (l r : Aux α → k) (h : auxLift U * X = Y * auxLift U)
    (hl : l ᵥ* U = l) (hr : U *ᵥ r = r) :
    close4 l r X = close4 l r Y := by
  have hL : (leftWall l : Matrix ι (AuxSite α ι) k) * auxLift U = leftWall l := by
    rw [leftWall_auxLift,hl]
  have hR : (auxLift U : Total α ι k) * rightWall r = rightWall r := by
    rw [auxLift_rightWall,hr]
  let Lw : Matrix ι (AuxSite α ι) k := leftWall l
  let Rw : Matrix (AuxSite α ι) ι k := rightWall r
  let E : Total α ι k := auxLift U
  have hL' : Lw * E = Lw := hL
  have hR' : E * Rw = Rw := hR
  change Lw * X * Rw = Lw * Y * Rw
  calc
    _ = (Lw * E) * X * Rw := by rw [hL']
    _ = Lw * (E * X) * Rw := by simp only [Matrix.mul_assoc]
    _ = Lw * (Y * E) * Rw := by rw [h]
    _ = (Lw * Y) * (E * Rw) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hR']
noncomputable def auxBC (F : Matrix (α×α) (α×α) k) : Matrix (Aux α) (Aux α) k :=
  fun p q => F (p.2.1,p.2.2.1) (q.2.1,q.2.2.1) *
    (1 : Matrix α α k) p.1 q.1 * (1 : Matrix α α k) p.2.2.2 q.2.2.2
noncomputable def auxAC (F : Matrix (α×α) (α×α) k) : Matrix (Aux α) (Aux α) k :=
  fun p q => F (p.1,p.2.2.1) (q.1,q.2.2.1) *
    (1 : Matrix α α k) p.2.1 q.2.1 * (1 : Matrix α α k) p.2.2.2 q.2.2.2
noncomputable def auxBD (F : Matrix (α×α) (α×α) k) : Matrix (Aux α) (Aux α) k :=
  fun p q => F (p.2.1,p.2.2.2) (q.2.1,q.2.2.2) *
    (1 : Matrix α α k) p.1 q.1 * (1 : Matrix α α k) p.2.2.1 q.2.2.1
noncomputable def auxAD (F : Matrix (α×α) (α×α) k) : Matrix (Aux α) (Aux α) k :=
  fun p q => F (p.1,p.2.2.2) (q.1,q.2.2.2) *
    (1 : Matrix α α k) p.2.1 q.2.1 * (1 : Matrix α α k) p.2.2.1 q.2.2.1
omit [Fintype α] [Fintype ι] in
lemma exBC_aux (F : Matrix (α×α) (α×α) k) :
    (exBC F : Total α ι k) = auxLift (auxBC F) := rfl
omit [Fintype α] [Fintype ι] in
lemma exAC_aux (F : Matrix (α×α) (α×α) k) :
    (exAC F : Total α ι k) = auxLift (auxAC F) := rfl
omit [Fintype α] [Fintype ι] in
lemma exBD_aux (F : Matrix (α×α) (α×α) k) :
    (exBD F : Total α ι k) = auxLift (auxBD F) := rfl
omit [Fintype α] [Fintype ι] in
lemma exAD_aux (F : Matrix (α×α) (α×α) k) :
    (exAD F : Total α ι k) = auxLift (auxAD F) := rfl
noncomputable def auxTrain (F₁ F₂ F₃ F₄ : Matrix (α×α) (α×α) k) :
    Matrix (Aux α) (Aux α) k := auxAD F₄ * auxBD F₃ * auxAC F₂ * auxBC F₁
lemma auxTrain_lift (F₁ F₂ F₃ F₄ : Matrix (α×α) (α×α) k) :
    (auxLift (auxTrain F₁ F₂ F₃ F₄) : Total α ι k) =
      exAD F₄ * exBD F₃ * exAC F₂ * exBC F₁ := by
  simp only [auxTrain,auxLift_mul,exAD_aux,exBD_aux,exAC_aux,exBC_aux]
end
end CriticalHoneycomb.Transfer.ClosedFourRow

end

section

namespace CriticalHoneycomb.Transfer.ClosedFourRow
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
section
variable {α ι k : Type*} [CommSemiring k] [Fintype α] [DecidableEq α]
  [Fintype ι] [DecidableEq ι]
noncomputable def pairAB (P : ι → ι → Matrix (α×α) (α×α) k) : Total α ι k :=
  fun p q => P p.2 q.2 (p.1.1,p.1.2.1) (q.1.1,q.1.2.1) *
    (1 : Matrix α α k) p.1.2.2.1 q.1.2.2.1 *
    (1 : Matrix α α k) p.1.2.2.2 q.1.2.2.2
noncomputable def pairCD (P : ι → ι → Matrix (α×α) (α×α) k) : Total α ι k :=
  fun p q => P p.2 q.2 (p.1.2.2.1,p.1.2.2.2) (q.1.2.2.1,q.1.2.2.2) *
    (1 : Matrix α α k) p.1.1 q.1.1 * (1 : Matrix α α k) p.1.2.1 q.1.2.1
omit [DecidableEq ι] in
lemma pairAB_forward (M N : Row α ι k) : rowA M * rowB N = pairAB (forwardPair M N) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [rowA,rowB,pairAB,forwardPair,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap,Matrix.one_apply,mul_ite,ite_mul,
    Matrix.sum_apply,Matrix.of_apply]
omit [DecidableEq ι] in
lemma pairCD_forward (M N : Row α ι k) : rowC M * rowD N = pairCD (forwardPair M N) := by
  ext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [rowC,rowD,pairCD,forwardPair,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap,Matrix.one_apply,mul_ite,ite_mul,
    Matrix.sum_apply,Matrix.of_apply]
omit [DecidableEq ι] in
lemma pairAB_mul_CD (P Q : ι → ι → Matrix (α×α) (α×α) k)
    (a b c d a' b' c' d' : α) (s t : ι) :
    (pairAB P * pairCD Q) ((a,b,c,d),s) ((a',b',c',d'),t) =
      ∑ v, P s v (a,b) (a',b') * Q v t (c,d) (c',d') := by
  simp [pairAB,pairCD,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul]
omit [DecidableEq ι] in
lemma pairCD_mul_AB (P Q : ι → ι → Matrix (α×α) (α×α) k)
    (a b c d a' b' c' d' : α) (s t : ι) :
    (pairCD Q * pairAB P) ((a,b,c,d),s) ((a',b',c',d'),t) =
      ∑ v, P v t (a,b) (a',b') * Q s v (c,d) (c',d') := by
  simp [pairAB,pairCD,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    mul_ite,ite_mul,mul_comm]
noncomputable def tensorBoundary (l₁ l₂ : α×α → k) : Aux α → k :=
  fun p => l₁ (p.1,p.2.1) * l₂ (p.2.2.1,p.2.2.2)
noncomputable def closePair (P : ι → ι → Matrix (α×α) (α×α) k)
    (l r : α×α → k) : Matrix ι ι k := fun s t => ∑ p, ∑ q, l p * P s t p q * r q
omit [DecidableEq α] in
lemma close4_apply (l r : Aux α → k) (X : Total α ι k) (s t : ι) :
    close4 l r X s t = ∑ p, ∑ q, l p * X (p,s) (q,t) * r q := by
  have hR (p : AuxSite α ι) :
      (X * (rightWall r : Matrix (AuxSite α ι) ι k)) p t = ∑ q, X p (q,t) * r q := by
    rw [Matrix.mul_apply,Fintype.sum_prod_type]
    simp [rightWall,Matrix.one_apply,mul_ite]
  rw [close4,Matrix.mul_assoc,Matrix.mul_apply,Fintype.sum_prod_type]
  simp [leftWall,Matrix.one_apply,mul_ite,ite_mul,hR,Finset.mul_sum,mul_assoc]
omit [DecidableEq α] in
lemma sum_aux (f : Aux α → k) :
    ∑ p, f p = ∑ p : α×α, ∑ q : α×α, f (p.1,p.2,q.1,q.2) := by
  simp [Fintype.sum_prod_type]

lemma five_sum_factor {β₁ β₂ β₃ β₄ ν : Type*}
    [Fintype β₁] [Fintype β₂] [Fintype β₃] [Fintype β₄] [Fintype ν]
    (F : ν → β₁ → β₃ → k) (G : ν → β₂ → β₄ → k) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ v, F v a c * G v b d) =
      ∑ v, (∑ a, ∑ c, F v a c) * (∑ b, ∑ d, G v b d) := by
  conv_lhs =>
    enter [2,a,2,b,2,c]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2,a,2,b]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2,a]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
lemma close4_pair_product (P Q : ι → ι → Matrix (α×α) (α×α) k)
    (l₁ l₂ r₁ r₂ : α×α → k) :
    close4 (tensorBoundary l₁ l₂) (tensorBoundary r₁ r₂) (pairAB P * pairCD Q) =
      closePair P l₁ r₁ * closePair Q l₂ r₂ := by
  ext s t
  rw [close4_apply]
  simp only [sum_aux,tensorBoundary,pairAB_mul_CD]
  rw [Matrix.mul_apply]
  simp only [closePair]
  convert five_sum_factor
    (fun v a c => l₁ a * P s v a c * r₁ c)
    (fun v b d => l₂ b * Q v t b d * r₂ d) using 1
  simp only [Finset.mul_sum,Finset.sum_mul]
  repeat first | apply Finset.sum_congr rfl; intro _ _ | ring

lemma close4_pair_reverse (P Q : ι → ι → Matrix (α×α) (α×α) k)
    (l₁ l₂ r₁ r₂ : α×α → k) :
    close4 (tensorBoundary l₁ l₂) (tensorBoundary r₁ r₂) (pairCD Q * pairAB P) =
      closePair Q l₂ r₂ * closePair P l₁ r₁ := by
  ext s t
  rw [close4_apply]
  simp only [sum_aux,tensorBoundary,pairCD_mul_AB]
  rw [Matrix.mul_apply]
  simp only [closePair]
  calc
    _ = ∑ v, (∑ a, ∑ c, l₁ a * P v t a c * r₁ c) *
        (∑ b, ∑ d, l₂ b * Q s v b d * r₂ d) := by
      convert five_sum_factor
        (fun v a c => l₁ a * P v t a c * r₁ c)
        (fun v b d => l₂ b * Q s v b d * r₂ d) using 1
      simp only [Finset.mul_sum,Finset.sum_mul]
      repeat first | apply Finset.sum_congr rfl; intro _ _ | ring
    _ = _ := by apply Finset.sum_congr rfl; intro v hv; exact mul_comm _ _

theorem closed_four_train (A B C D : Row α ι k)
    (F₁ F₂ F₃ F₄ : Matrix (α×α) (α×α) k)
    (l₁ l₂ r₁ r₂ : α×α → k)
    (h₁ : ∀ s t, F₁ * forwardPair B C s t = backwardPair B C s t * F₁)
    (h₂ : ∀ s t, F₂ * forwardPair A C s t = backwardPair A C s t * F₂)
    (h₃ : ∀ s t, F₃ * forwardPair B D s t = backwardPair B D s t * F₃)
    (h₄ : ∀ s t, F₄ * forwardPair A D s t = backwardPair A D s t * F₄)
    (hl : tensorBoundary l₁ l₂ ᵥ* auxTrain F₁ F₂ F₃ F₄ = tensorBoundary l₁ l₂)
    (hr : auxTrain F₁ F₂ F₃ F₄ *ᵥ tensorBoundary r₁ r₂ = tensorBoundary r₁ r₂) :
    Commute (closePair (forwardPair A B) l₁ r₁) (closePair (forwardPair C D) l₂ r₂) := by
  have ht := lifted_four_train A B C D F₁ F₂ F₃ F₄ h₁ h₂ h₃ h₄
  rw [←auxTrain_lift] at ht
  have hc := close_train _ _ _ _ _ ht hl hr
  have hAB := pairAB_forward A B
  have hCD := pairCD_forward C D
  have he : rowA A * rowB B * rowC C * rowD D =
      pairAB (forwardPair A B) * pairCD (forwardPair C D) := by
    rw [←hAB,←hCD]; simp only [Matrix.mul_assoc]
  have he' : rowC C * rowD D * rowA A * rowB B =
      pairCD (forwardPair C D) * pairAB (forwardPair A B) := by
    rw [←hAB,←hCD]; simp only [Matrix.mul_assoc]
  rw [he,he',close4_pair_product,close4_pair_reverse] at hc
  exact hc

end
end CriticalHoneycomb.Transfer.ClosedFourRow

end

section
namespace CriticalHoneycomb.Transfer.ClosedFourRow
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {α ι k : Type*} [Fintype α] [DecidableEq α] [Fintype ι]
  [CommSemiring k]
noncomputable def pairSwap : Matrix (α×α) (α×α) k :=
  fun p q=> if p=(q.2,q.1) then 1 else 0
lemma pairSwap_mulVec (v : α×α→k) (p : α×α) :
    (pairSwap *ᵥ v) p=v (p.2,p.1) := by
  classical
  simp [pairSwap,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Prod.ext_iff,ite_and]
lemma pairSwap_sq : (pairSwap : Matrix (α×α) (α×α) k)*pairSwap=1 := by
  classical
  funext p q
  simp [pairSwap,Matrix.mul_apply,Fintype.sum_prod_type,Prod.ext_iff,Matrix.one_apply,ite_and]
omit [Fintype α] in
lemma pairSwap_transpose : (pairSwap : Matrix (α×α) (α×α) k)ᵀ=pairSwap := by
  classical
  funext p q
  simp [pairSwap,Matrix.transpose_apply,Prod.ext_iff,eq_comm,and_comm]
lemma pairSwap_mul (M : Matrix (α×α) (α×α) k) (p q : α×α) :
    (pairSwap*M : Matrix (α×α) (α×α) k) p q=M (p.2,p.1) q := by
  classical
  simp [pairSwap,Matrix.mul_apply,Fintype.sum_prod_type,Prod.ext_iff,ite_mul,ite_and]
lemma mul_pairSwap (M : Matrix (α×α) (α×α) k) (p q : α×α) :
    (M*pairSwap : Matrix (α×α) (α×α) k) p q=M p (q.2,q.1) := by
  classical
  simp [pairSwap,Matrix.mul_apply,Fintype.sum_prod_type,Prod.ext_iff,mul_ite,ite_and]
lemma pairSwap_conjugate (M : Matrix (α×α) (α×α) k) (p q : α×α) :
    (pairSwap*M*pairSwap : Matrix (α×α) (α×α) k) p q=M (p.2,p.1) (q.2,q.1) := by
  classical
  simp [pairSwap,Matrix.mul_apply,Fintype.sum_prod_type,Prod.ext_iff,ite_mul,mul_ite,ite_and]
lemma swap_backward (X Y : Row α ι k) (s t : ι) :
    pairSwap * backwardPair X Y s t * pairSwap = forwardPair Y X s t := by
  funext p q
  simp only [pairSwap_conjugate,backwardPair,forwardPair,Matrix.sum_apply,
    Matrix.kronecker,Matrix.kroneckerMap,Matrix.of_apply,mul_comm]
lemma closed_pair_reflection (R F B : Matrix (α×α) (α×α) k)
    (v w v' w' : α×α→k)
    (hE : R*F=B*R) (hPT : Rᵀ*pairSwap=pairSwap*R)
    (hv : R*ᵥv'=pairSwap*ᵥv) (hw : R*ᵥw=pairSwap*ᵥw') :
    v ⬝ᵥ (F*ᵥw) = v' ⬝ᵥ ((pairSwap*B*pairSwap)*ᵥw') := by
  have hv' : v=(pairSwap*R)*ᵥv' := by
    rw [←Matrix.mulVec_mulVec,hv,Matrix.mulVec_mulVec,pairSwap_sq,Matrix.one_mulVec]
  rw [hv']
  calc
    _=v' ⬝ᵥ ((Rᵀ*pairSwap)*ᵥ(F*ᵥw)) := by
      conv_rhs => rw [←pairSwap_transpose,←Matrix.transpose_mul]
      conv_rhs => rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
    _=v' ⬝ᵥ ((pairSwap*R*F)*ᵥw) := by
      rw [hPT,Matrix.mulVec_mulVec]
    _=v' ⬝ᵥ ((pairSwap*B*R)*ᵥw) := by rw [Matrix.mul_assoc,hE,←Matrix.mul_assoc]
    _=v' ⬝ᵥ ((pairSwap*B*pairSwap)*ᵥw') := by
      rw [←Matrix.mulVec_mulVec,hw,Matrix.mulVec_mulVec]
omit [DecidableEq α] [Fintype ι] in
lemma closePair_dot (F : ι→ι→Matrix (α×α) (α×α) k) (v w : α×α→k) (s t : ι) :
    closePair F v w s t=v ⬝ᵥ (F s t*ᵥw) := by
  simp only [closePair,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
end CriticalHoneycomb.Transfer.ClosedFourRow

end

end OAI
