import Mathlib

namespace OAI

section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℚ R]

def ncDerivative : PowerSeries R→ₗ[ℚ] PowerSeries R where
  toFun F:=PowerSeries.mk (fun n=>(n+1) • coeff (n+1) F)
  map_add' F G:=by ext n; simp
  map_smul' a F:=by ext n; simp

@[simp] lemma coeff_ncDerivative (F : PowerSeries R) (n : ℕ) :
    coeff n (ncDerivative F)=(n+1) • coeff (n+1) F := by simp [ncDerivative]

@[simp] lemma ncDerivative_one : ncDerivative (1 : PowerSeries R)=0 := by
  ext n
  simp

lemma ncDerivative_mul (F G : PowerSeries R) :
    ncDerivative (F*G)=ncDerivative F*G+F*ncDerivative G := by
  ext n
  simp only [coeff_ncDerivative,coeff_mul,map_add]
  rw [Finset.smul_sum]
  have H : (∑p∈Finset.HasAntidiagonal.antidiagonal (n+1),
      (n+1) • (coeff p.1 F*coeff p.2 G))=
      (∑p∈Finset.HasAntidiagonal.antidiagonal (n+1),
        p.1 • (coeff p.1 F*coeff p.2 G))+
      (∑p∈Finset.HasAntidiagonal.antidiagonal (n+1),
        p.2 • (coeff p.1 F*coeff p.2 G)) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [←add_nsmul,Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  rw [H,Finset.Nat.sum_antidiagonal_succ,Finset.Nat.sum_antidiagonal_succ']
  simp only [zero_nsmul,zero_add,smul_mul_assoc,mul_smul_comm]

omit [Algebra ℚ R] in
lemma coeff_power_vanish (F : PowerSeries R) (hF : constantCoeff F=0)
    (k n : ℕ) (h : n<k) : coeff n (F^k)=0 := by
  induction k generalizing n with
  | zero=>omega
  | succ k ih=>
    rw [pow_succ,coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    by_cases h0 : p.2=0
    · rw [h0,coeff_zero_eq_constantCoeff,hF,mul_zero]
    · rw [ih p.1 (by omega),zero_mul]

variable {K : Type*} [CommRing K] [Algebra ℚ K]
def traceSeries (τ : R→ₗ[ℚ] K) : PowerSeries R→ₗ[ℚ] PowerSeries K where
  toFun F:=PowerSeries.mk (fun n=>τ (coeff n F))
  map_add' F G:=by ext n; simp
  map_smul' a F:=by ext n; simp

@[simp] lemma coeff_traceSeries (τ : R→ₗ[ℚ] K) (F : PowerSeries R) (n : ℕ) :
    coeff n (traceSeries τ F)=τ (coeff n F) := by simp [traceSeries]

variable (τ : R→ₗ[ℚ] K) (hτ : ∀a b,τ (a*b)=τ (b*a))
include hτ in
lemma traceSeries_cyclic (F G : PowerSeries R) : traceSeries τ (F*G)=traceSeries τ (G*F) := by
  ext n
  simp only [coeff_traceSeries,coeff_mul,map_sum]
  rw [←Finset.Nat.sum_antidiagonal_swap (f:=fun p=>τ (coeff p.1 G*coeff p.2 F))]
  apply Finset.sum_congr rfl
  intro p hp
  exact hτ _ _

include hτ in
lemma trace_derivative_power (F : PowerSeries R) (k l : ℕ) :
    traceSeries τ (ncDerivative (F^(k+1))*F^l)=
      (k+1) • traceSeries τ (ncDerivative F*F^(k+l)) := by
  induction k generalizing l with
  | zero=>simp
  | succ k ih=>
    rw [pow_succ (F) (k+1),ncDerivative_mul,add_mul,map_add]
    have H1 : ncDerivative (F^(k+1))*F*F^l=ncDerivative (F^(k+1))*F^(l+1) := by
      rw [mul_assoc,←pow_succ']
    rw [H1,ih]
    have H2 : traceSeries τ (F^(k+1)*ncDerivative F*F^l)=
        traceSeries τ (ncDerivative F*F^(k+1+l)) := by
      rw [mul_assoc,traceSeries_cyclic τ hτ, mul_assoc,←pow_add]
      rw [Nat.add_comm l (k+1)]
    rw [H2]
    have heq : k+(l+1)=k+1+l := by omega
    simp only [heq,add_nsmul,one_nsmul]

include hτ in
lemma trace_derivative_power' (F : PowerSeries R) (k : ℕ) :
    traceSeries τ (ncDerivative (F^(k+1)))=
      (k+1) • traceSeries τ (ncDerivative F*F^k) := by
  simpa using trace_derivative_power τ hτ F k 0
end
end ElementaryPositivity.FormalLog

end
section
namespace ElementaryPositivity.FormalLog
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]
lemma inverse_geometric_coeff (F : PowerSeries R) (hF : constantCoeff F=1) (n : ℕ) :
    coeff n (invOfUnit F 1)=coeff n (∑k∈Finset.range (n+1),(-(F-1))^k) := by
  let U:=-(F-1)
  have hU : constantCoeff U=0:=by simp [U,hF]
  have heq : 1-U=F := by dsimp [U]; abel
  have H : (∑k∈Finset.range (n+1),U^k)*F=1-U^(n+1) := by
    rw [←heq]
    exact geom_sum_mul_neg U (n+1)
  have HI : F*invOfUnit F 1=1:=mul_invOfUnit F 1 hF
  have H' := congrArg (fun x : PowerSeries R=>x*invOfUnit F 1) H
  rw [mul_assoc,HI,mul_one,sub_mul,one_mul] at H'
  have Hzero : coeff n (U^(n+1)*invOfUnit F 1)=0 := by
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    rw [coeff_power_vanish U hU (n+1) p.1 (by
      have :=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      omega),zero_mul]
  have HH:=congrArg (coeff n) H'
  rw [map_sub,Hzero,sub_zero] at HH
  exact HH.symm

lemma geometric_mul_coeff (F A : PowerSeries R) (hF : constantCoeff F=1) (n : ℕ) :
    coeff n (A*invOfUnit F 1)=
      coeff n (A*(∑k∈Finset.range (n+1),(-(F-1))^k)) := by
  rw [coeff_mul,coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  have H:=Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [inverse_geometric_coeff F hF p.2]
  simp only [map_sum]
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkn
  exact coeff_power_vanish (-(F-1)) (by simp [hF]) k p.2
    (by simp only [Finset.mem_range] at hkn; omega)
end
end ElementaryPositivity.FormalLog

end

end OAI
