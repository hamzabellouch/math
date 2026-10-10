import Mathlib
import OAI.Combinatorics.Chromatic.Walls.CompletedInverse
import OAI.Combinatorics.Chromatic.GradedAlgebra.RootTruncation

namespace OAI

section
namespace ElementaryPositivity.PowerSeriesAdjoint
open PowerSeries RootTruncation
noncomputable section
variable {A : Type*} [Ring A]
lemma cut_eq_monomial_sum (X : PowerSeries A) (N : ℕ) :
    cut N X=∑j∈Finset.range (N+1),monomial j (coeff j X) := by
  classical
  ext n
  rw [coeff_cut,map_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range,Nat.lt_succ_iff]
lemma adjoint_add (F X Y : PowerSeries A) : adjoint F (X+Y)=adjoint F X+adjoint F Y := by
  simp only [adjoint,mul_add,add_mul]
lemma adjoint_zero (F : PowerSeries A) : adjoint F 0=0 := by simp [adjoint]
lemma adjoint_sum {J : Type*} (F : PowerSeries A) (s : Finset J) (X : J → PowerSeries A) :
    adjoint F (∑j∈s,X j)=∑j∈s,adjoint F (X j) := by
  simp only [adjoint,Finset.mul_sum,Finset.sum_mul]
lemma monomial_C_X (j : ℕ) (a : A) : monomial j a=PowerSeries.C a*PowerSeries.X^j := by
  ext n
  rw [coeff_monomial,coeff_C_mul_X_pow]
lemma adjoint_X_pow (F X : PowerSeries A) (j : ℕ) :
    adjoint F (X*PowerSeries.X^j)=adjoint F X*PowerSeries.X^j := by
  simp only [adjoint,mul_assoc]
  rw [X_pow_mul]
lemma adjoint_monomial (F : PowerSeries A) (j : ℕ) (a : A) :
    adjoint F (monomial j a)=adjoint F (PowerSeries.C a)*PowerSeries.X^j := by
  rw [monomial_C_X,adjoint_X_pow]
lemma coeff_adjoint_expansion (F X : PowerSeries A) (N : ℕ) :
    coeff N (adjoint F X)=∑j∈Finset.range (N+1),coeff (N-j) (adjoint F (PowerSeries.C (coeff j X))) := by
  classical
  rw [adjoint_coeff_congr F F X (cut N X) N (fun _ _=>rfl)
    (fun j hj=>(coeff_cut_of_le X hj).symm),cut_eq_monomial_sum,adjoint_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [adjoint_monomial,coeff_mul_X_pow',ite_eq_left (by have H:=Finset.mem_range.mp hj; omega)]
lemma coeff_adjoint_lower (F X : PowerSeries A) (hF : constantCoeff F=1) (N : ℕ) :
    coeff N (adjoint F X)=coeff N X+
      ∑j∈Finset.range N,coeff (N-j) (adjoint F (PowerSeries.C (coeff j X))) := by
  rw [coeff_adjoint_expansion,Finset.sum_range_succ,Nat.sub_self,coeff_zero_eq_constantCoeff,
    constant_adjoint F _ hF,constantCoeff_C,add_comm]
variable {R : Type*} [CommRing R] [Algebra R A]
lemma adjoint_smul (F X : PowerSeries A) (r : R) : adjoint F (r • X)=r • adjoint F X := by
  simp only [adjoint,mul_smul_comm,smul_mul_assoc]
end
end ElementaryPositivity.PowerSeriesAdjoint

end

end OAI
