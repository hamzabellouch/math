import OAI.Combinatorics.PolynomialVacuum.Algebra.Target

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

section Generic
variable {R I : Type*} [CommRing R] [DecidableEq I]

abbrev SpinTensor (I R : Type*) := (I → Spin) → R

def replacePair (s : I → Spin) (i j : I) (ab : Pair) : I → Spin :=
  Function.update (Function.update s i ab.1) j ab.2

@[simp] theorem replacePair_left (s : I → Spin) {i j : I} (hij : i≠j) (ab : Pair) :
    replacePair s i j ab i=ab.1 := by simp [replacePair,hij]
@[simp] theorem replacePair_right (s : I → Spin) (i j : I) (ab : Pair) :
    replacePair s i j ab j=ab.2 := by simp [replacePair]
@[simp] theorem replacePair_other (s : I → Spin) {i j k : I} (hi : k≠i) (hj : k≠j) (ab : Pair) :
    replacePair s i j ab k=s k := by simp [replacePair,hi,hj]
@[simp] theorem replacePair_replacePair (s : I → Spin) (i j : I) (ab cd : Pair) :
    replacePair (replacePair s i j ab) i j cd=replacePair s i j cd := by
  funext k
  by_cases hk : k=j
  · subst k; simp [replacePair]
  · by_cases hi : k=i
    · subst k; simp [replacePair,hk]
    · simp [replacePair,hk,hi]

def pairAction (i j : I) (A : Matrix Pair Pair R) (W : SpinTensor I R) : SpinTensor I R :=
  fun s => ∑ ab : Pair, A (s i,s j) ab * W (replacePair s i j ab)

theorem pairAction_mul {i j : I} (hij : i≠j) (A B : Matrix Pair Pair R) (W : SpinTensor I R) :
    pairAction i j A (pairAction i j B W)=pairAction i j (A*B) W := by
  funext s
  simp only [pairAction,replacePair_left s hij,replacePair_right,replacePair_replacePair,
    Finset.mul_sum,Matrix.mul_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ab _
  apply Finset.sum_congr rfl
  intro cd _
  simp only [mul_assoc]

theorem pairAction_smul (i j : I) (c : R) (A : Matrix Pair Pair R) (W : SpinTensor I R) :
    pairAction i j (c • A) W=fun s => c*pairAction i j A W s := by
  funext s
  simp only [pairAction,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]

theorem pairAction_scalar (i j : I) (c : R) (A : Matrix Pair Pair R) (W : SpinTensor I R) :
    pairAction i j A (fun s => c*W s)=fun s => c*pairAction i j A W s := by
  funext s
  simp only [pairAction,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab _
  ring

theorem replacePair_self (s : I → Spin) (i j : I) : replacePair s i j (s i,s j)=s := by
  simp [replacePair]

theorem pairAction_one (i j : I) (W : SpinTensor I R) : pairAction i j 1 W=W := by
  funext s
  simp [pairAction,Matrix.one_apply,replacePair_self]

theorem replacePair_comm (s : I → Spin) {i j k l : I}
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) (ab cd : Pair) :
    replacePair (replacePair s i j ab) k l cd=replacePair (replacePair s k l cd) i j ab := by
  funext r
  by_cases hri : r=i
  · subst r; simp [replacePair,Function.update_apply,hik,hil]
  · by_cases hrj : r=j
    · subst r; simp [replacePair,hjk,hjl]
    · by_cases hrk : r=k
      · subst r; simp [replacePair,Function.update_apply,hri,hrj]
      · by_cases hrl : r=l
        · subst r; simp [replacePair,hri,hrj]
        · simp [replacePair,hri,hrj,hrk,hrl]

theorem pairAction_comm {i j k l : I}
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l)
    (A B : Matrix Pair Pair R) (W : SpinTensor I R) :
    pairAction i j A (pairAction k l B W)=pairAction k l B (pairAction i j A W) := by
  funext s
  simp only [pairAction,replacePair_other s (Ne.symm hik) (Ne.symm hjk),
    replacePair_other s (Ne.symm hil) (Ne.symm hjl), replacePair_other s hik hil,
    replacePair_other s hjk hjl,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro cd _
  apply Finset.sum_congr rfl
  intro ab _
  rw [replacePair_comm s hik hil hjk hjl]
  ring

end Generic
end PolynomialVacuumAlgebra

end OAI
