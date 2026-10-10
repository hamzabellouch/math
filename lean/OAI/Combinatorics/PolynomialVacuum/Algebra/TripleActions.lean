import OAI.Combinatorics.PolynomialVacuum.Algebra.TensorActions

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical
abbrev Triple := Spin × Spin × Spin

section Generic
variable {R I : Type*} [CommRing R] [DecidableEq I]

def replaceTriple (s : I → Spin) (i j k : I) (abc : Triple) : I → Spin :=
  Function.update (replacePair s i j (abc.1,abc.2.1)) k abc.2.2

@[simp] theorem replaceTriple_first (s : I → Spin) {i j k : I}
    (hij : i≠j) (hik : i≠k) (abc : Triple) : replaceTriple s i j k abc i=abc.1 := by
  simp [replaceTriple,hik,replacePair_left s hij]
@[simp] theorem replaceTriple_middle (s : I → Spin) {i j k : I}
    (hjk : j≠k) (abc : Triple) : replaceTriple s i j k abc j=abc.2.1 := by
  simp [replaceTriple,hjk]
@[simp] theorem replaceTriple_last (s : I → Spin) (i j k : I) (abc : Triple) :
    replaceTriple s i j k abc k=abc.2.2 := by simp [replaceTriple]
@[simp] theorem replaceTriple_replaceTriple (s : I → Spin) (i j k : I) (abc def' : Triple) :
    replaceTriple (replaceTriple s i j k abc) i j k def'=replaceTriple s i j k def' := by
  funext r
  simp only [replaceTriple,replacePair,Function.update_apply]
  split_ifs <;> rfl

def tripleAction (i j k : I) (A : Matrix Triple Triple R) (W : SpinTensor I R) : SpinTensor I R :=
  fun s => ∑ abc : Triple, A (s i,s j,s k) abc * W (replaceTriple s i j k abc)

theorem tripleAction_mul {i j k : I} (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (A B : Matrix Triple Triple R) (W : SpinTensor I R) :
    tripleAction i j k A (tripleAction i j k B W)=tripleAction i j k (A*B) W := by
  funext s
  simp only [tripleAction,replaceTriple_first s hij hik,replaceTriple_middle s hjk,
    replaceTriple_last,replaceTriple_replaceTriple,Finset.mul_sum,Matrix.mul_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro abc _
  apply Finset.sum_congr rfl
  intro def' _
  simp only [mul_assoc]

def matrix12 (A : Matrix Pair Pair R) : Matrix Triple Triple R :=
  fun a b => if a.2.2=b.2.2 then A (a.1,a.2.1) (b.1,b.2.1) else 0

def matrix23 (A : Matrix Pair Pair R) : Matrix Triple Triple R :=
  fun a b => if a.1=b.1 then A a.2 b.2 else 0

theorem tripleAction_matrix12 {i j k : I} (hik : i≠k) (hjk : j≠k)
    (A : Matrix Pair Pair R) (W : SpinTensor I R) :
    tripleAction i j k (matrix12 A) W=pairAction i j A W := by
  funext s
  have h (a b : Spin) : replaceTriple s i j k (a,b,s k)=replacePair s i j (a,b) := by
    funext r
    by_cases hr : r=k
    · subst r
      simp [replaceTriple,replacePair,Ne.symm hik,Ne.symm hjk]
    · simp [replaceTriple,hr]
  simp [tripleAction,matrix12,pairAction,Fintype.sum_prod_type,ite_mul,h]

theorem tripleAction_matrix23 (i j k : I) (A : Matrix Pair Pair R) (W : SpinTensor I R) :
    tripleAction i j k (matrix23 A) W=pairAction j k A W := by
  funext s
  have h (b c : Spin) : replaceTriple s i j k (s i,b,c)=replacePair s j k (b,c) := by
    simp [replaceTriple,replacePair]
  simp [tripleAction,matrix23,pairAction,Fintype.sum_prod_type,ite_mul,h]

theorem matrix121_apply (A B C : Matrix Pair Pair R) (a b c d e f : Spin) :
    (matrix12 A * matrix23 B * matrix12 C) (a,b,c) (d,e,f) =
      ∑ i : Spin, ∑ j : Spin, ∑ k : Spin, A (a,b) (i,j) * B (j,c) (k,f) * C (i,k) (d,e) := by
  simp only [Matrix.mul_apply,matrix12,matrix23,Fintype.sum_prod_type,
    Finset.sum_mul,ite_mul,mul_ite,zero_mul,mul_zero]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem matrix232_apply (A B C : Matrix Pair Pair R) (a b c d e f : Spin) :
    (matrix23 A * matrix12 B * matrix23 C) (a,b,c) (d,e,f) =
      ∑ i : Spin, ∑ j : Spin, ∑ k : Spin, A (b,c) (j,k) * B (a,j) (d,i) * C (i,k) (e,f) := by
  simp only [Matrix.mul_apply,matrix12,matrix23,Fintype.sum_prod_type,
    Finset.sum_mul,ite_mul,mul_ite,zero_mul,mul_zero]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

end Generic
end PolynomialVacuumAlgebra

end OAI
