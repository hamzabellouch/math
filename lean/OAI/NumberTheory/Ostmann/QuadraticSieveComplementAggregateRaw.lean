import OAI.NumberTheory.Ostmann.QuadraticSieveComplementAggregateDivisors
import OAI.NumberTheory.Ostmann.QuadraticSieveComplementAggregateNorm

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped ArithmeticFunction.Moebius

def complementKernelSum (M : ℝ) (K Δ N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ)
    (g : ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ r ∈ (2*Δ).divisors, ∑ d ∈ Finset.Icc 1 (N^2), ∑ v ∈ oddSquarefreeUpTo K,
    (μ r:ℂ)*(μ d:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*d):ℝ):ℂ)*g r d v*
      coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ)

theorem complement_raw_sum_bound {ξ : ℝ} (hξ1 : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M T A : ℝ) (K Δ N : ℕ) (S : Finset ℕ)
      (a : ℕ → ℂ) (g : ℕ → ℕ → ℕ → ℂ),
      0 < M → 1 ≤ T → 0 ≤ A → 0 < K → 0 < Δ → 0 < N → S ⊆ oddSquarefreeUpTo N →
      (∀ r ∈ (2*Δ).divisors, ∀ d, ∀ v ∈ oddSquarefreeUpTo K, ‖g r d v‖ ≤ A) →
      (∀ r ∈ (2*Δ).divisors, ∀ d, ∀ v ∈ oddSquarefreeUpTo K, g r d v ≠ 0 →
        complementWindowLower M T v < (r*d:ℕ)) →
      ‖complementKernelSum M K Δ N S a g‖ ≤
        C*A*(Nat.log 2 K+1:ℕ)*(Nat.log 2 (N^2)+2:ℕ)*(2*(K:ℝ)*N)^δ*(N:ℝ)^δ*
          (Δ:ℝ)^2*T*((N:ℝ)+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a := by
  classical
  obtain ⟨Cd,hCd,hdiv⟩ := complement_divisor_sum_bound δ hδ
  obtain ⟨Cn,hCn,hnorm⟩ := complement_binary_smaller_norm hξ δ hδ
  refine ⟨64*Cd*Cn,by positivity,?_⟩
  intro M T A K Δ N S a g hM hT hA hK hΔ hN hS hg hsupp
  have hE := coefficientEnergy_nonneg S a
  have hKr : (0:ℝ) < K := by exact_mod_cast hK
  have hΔ1 : (1:ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hNp : (0:ℝ) < N := by exact_mod_cast hN
  let H : ℝ := Cn*(2*(K:ℝ)*N)^δ
  let U : ℝ := (N:ℝ)+Real.sqrt M*(K:ℝ)^(ξ-1/2)
  let R : ℝ := (Nat.log 2 (N^2)+2:ℕ)*Cd*A*H*(N:ℝ)^δ*coefficientEnergy S a*(32*(Δ:ℝ)*T)*U
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hblock (r : ℕ) (hr : r ∈ (2*Δ).divisors)
      (j : ℕ) (hj : j ∈ Finset.range (Nat.log 2 K+1)) :
      ‖∑ d ∈ Finset.Icc 1 (N^2), ∑ v ∈ binarySquarefreeRows K j,
        (μ r:ℂ)*(μ d:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*d):ℝ):ℂ)*g r d v*
          coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ)‖ ≤ R := by
    have hvsub : binarySquarefreeRows K j ⊆ oddSquarefreeUpTo K := Finset.filter_subset _ _
    have hx : 0 ≤ (((2*2^j:ℕ):ℝ)^ξ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hh := hdiv M T (((2*2^j:ℕ):ℝ)^ξ) H A K j Δ r N S a (g r)
      hM hT hx hH hA hΔ hr hN hS
      (fun q hq => hnorm K N j q hK hN hq hj)
      (fun d v hv => hg r hr d v (hvsub hv))
      (fun d v hv hnz => hsupp r hr d v (hvsub hv) hnz)
    have hrr : (1:ℝ) ≤ r := by exact_mod_cast Nat.pos_of_mem_divisors hr
    have hratio : Cd*A*H/(r:ℝ) ≤ Cd*A*H := div_le_self (by positivity) hrr
    have hbK : ((2^j:ℕ):ℝ) ≤ K := by exact_mod_cast complement_binary_base_le hK hj
    have hscale := complement_binary_main_scale hM (by positivity : (0:ℝ)<(2^j:ℕ)) hbK hξ1 hξ2
    have hG : Real.sqrt (M/(2^j:ℕ))*(((2*2^j:ℕ):ℝ)^ξ)+(32*(Δ:ℝ)*T)*N ≤
        (32*(Δ:ℝ)*T)*U := by
      have hΔT : 1 ≤ (Δ:ℝ)*T := one_le_mul_of_one_le_of_one_le hΔ1 hT
      have hxmul := mul_le_mul_of_nonneg_right (show (4:ℝ) ≤ 32*(Δ:ℝ)*T by nlinarith)
        (show 0 ≤ Real.sqrt M*(K:ℝ)^(ξ-1/2) by positivity)
      push_cast at hscale
      dsimp [U]
      push_cast
      nlinarith
    refine hh.trans ?_
    calc
      _ ≤ (Nat.log 2 (N^2)+2:ℕ)*(Cd*A*H)*(N:ℝ)^δ*coefficientEnergy S a*
          ((32*(Δ:ℝ)*T)*U) := by
        gcongr
      _ = R := by dsimp [R]; ring
  have hrbound (r : ℕ) (hr : r ∈ (2*Δ).divisors) :
      ‖∑ d ∈ Finset.Icc 1 (N^2), ∑ v ∈ oddSquarefreeUpTo K,
        (μ r:ℂ)*(μ d:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*d):ℝ):ℂ)*g r d v*
          coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ)‖ ≤
        (Nat.log 2 K+1:ℕ)*R := by
    simp_rw [sum_oddSquarefree_eq_dyadic K]
    rw [Finset.sum_comm]
    apply (norm_sum_le _ _).trans
    exact (Finset.sum_le_sum (hblock r hr)).trans_eq (by simp [nsmul_eq_mul])
  have hcard : (2*Δ).divisors.card ≤ 2*Δ := by
    calc
      _ ≤ (Finset.Icc 1 (2*Δ)).card := Finset.card_le_card (by
        intro r hr
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hr,
          Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hr).1⟩)
      _ = _ := by simp
  unfold complementKernelSum
  calc
    _ ≤ ∑ r ∈ (2*Δ).divisors,
        ‖∑ d ∈ Finset.Icc 1 (N^2), ∑ v ∈ oddSquarefreeUpTo K,
          (μ r:ℂ)*(μ d:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*d):ℝ):ℂ)*g r d v*
            coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ)‖ := norm_sum_le _ _
    _ ≤ (2*Δ).divisors.card*((Nat.log 2 K+1:ℕ)*R) := by
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum hrbound
    _ ≤ (2*(Δ:ℝ))*((Nat.log 2 K+1:ℕ)*R) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by dsimp [R,H,U]; ring

end Ostmann.QuadraticSieve

end

end OAI
