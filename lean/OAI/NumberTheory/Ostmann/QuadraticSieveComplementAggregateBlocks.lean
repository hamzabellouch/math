import OAI.NumberTheory.Ostmann.QuadraticSieveComplementAggregateTransition
import OAI.NumberTheory.Ostmann.QuadraticSieveMainRemainderRows

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped ArithmeticFunction.Moebius

theorem complement_active_range_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M T x H A : ℝ) (K j Δ r D N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (g : ℕ → ℕ → ℂ),
      0 < M → 1 ≤ T → 0 ≤ x → 0 ≤ H → 0 ≤ A → 0 < Δ →
      r ∈ (2*Δ).divisors → 0 < D → 0 < N → S ⊆ oddSquarefreeUpTo N →
      (∀ q : ℕ, 0 < q → quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo (N/q)) ≤
        H*(x+(N:ℝ)/q)) →
      (∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j, ‖g d v‖ ≤ A) →
      (∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j, g d v ≠ 0 →
        complementWindowLower M T v < (r*d:ℕ)) →
      ‖∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ binarySquarefreeRows K j,
        (μ r:ℂ)*(μ d:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*d):ℝ):ℂ)*g d v*
          coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ)‖ ≤
        (2*A*H/(r:ℝ))*Real.sqrt (C*(N:ℝ)^ε*coefficientEnergy S a*coefficientEnergy S a)*
          (Real.sqrt (M/(2^j:ℕ))*x+(32*(Δ:ℝ)*T)*N) := by
  classical
  obtain ⟨C,hC,hbound⟩ := complementary_range_bootstrap_bound ε hε
  refine ⟨C,hC,?_⟩
  intro M T x H A K j Δ r D N S a g hM hT hx hH hA hΔ hr hD hN hS hnorm hg hsupp
  have hTp : 0 < T := by linarith
  have hΔ1 : (1:ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hΔeff : 1 ≤ 32*(Δ:ℝ)*T := by nlinarith [mul_le_mul hΔ1 hT (by norm_num) (by positivity)]
  have hrows : ∀ v ∈ binarySquarefreeRows K j, Odd v ∧ ((2^j:ℕ):ℝ) ≤ v := by
    intro v hv
    obtain ⟨hv',hlo,hhi⟩ := Finset.mem_filter.mp hv
    exact ⟨(mem_oddSquarefreeUpTo.mp hv').2.2.1,by exact_mod_cast hlo⟩
  by_cases hactive : ∃ d ∈ Finset.Ioc D (2*D), ∃ v ∈ binarySquarefreeRows K j, g d v ≠ 0
  · obtain ⟨d,hd,v,hv,hnz⟩ := hactive
    have ht := complement_block_transition hT hΔ hr hv (Finset.mem_Ioc.mp hd).2 (hsupp d hd v hv hnz)
    have hh := hbound D N (binarySquarefreeRows K j) S S a (fun n => conj (a n))
      M (2^j:ℕ) x H (32*(Δ:ℝ)*T) A r g hD hN hM (by positivity)
      hx hH hΔeff hA (Nat.pos_of_mem_divisors hr) hrows hS hS ht hnorm hg
    simpa only [coefficientEnergy_conj] using hh
  · have hz : ∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ binarySquarefreeRows K j, g d v = 0 := by
      intro d hd v hv
      by_contra hnz
      exact hactive ⟨d,hd,v,hv,hnz⟩
    have hsum : (∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ binarySquarefreeRows K j,
        (μ r:ℂ)*(μ d:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*d):ℝ):ℂ)*g d v*
          coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) d (v:ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      apply Finset.sum_eq_zero
      intro v hv
      rw [hz d hd v hv]
      ring
    rw [hsum,norm_zero]
    positivity

theorem complement_active_boundary_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M T x H A : ℝ) (K j Δ r N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (g : ℕ → ℂ),
      0 < M → 1 ≤ T → 0 ≤ x → 0 ≤ H → 0 ≤ A → 0 < Δ →
      r ∈ (2*Δ).divisors → 0 < N → S ⊆ oddSquarefreeUpTo N →
      quadraticNorm (binarySquarefreeRows K j) (oddSquarefreeUpTo N) ≤ H*(x+N) →
      (∀ v ∈ binarySquarefreeRows K j, ‖g v‖ ≤ A) →
      (∀ v ∈ binarySquarefreeRows K j, g v ≠ 0 → complementWindowLower M T v < (r*1:ℕ)) →
      ‖∑ v ∈ binarySquarefreeRows K j,
        (μ r:ℂ)*(μ 1:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*1):ℝ):ℂ)*g v*
          coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (v:ℤ)‖ ≤
        (A*C*H/(r:ℝ))*(N:ℝ)^ε*coefficientEnergy S a*
          (Real.sqrt (M/(2^j:ℕ))*x+(4*(Δ:ℝ)*T)*N) := by
  classical
  obtain ⟨C,hC,hbound⟩ := coprime_jacobi_L1_bound ε hε
  refine ⟨C,hC,?_⟩
  intro M T x H A K j Δ r N S a g hM hT hx hH hA hΔ hr hN hS hnorm hg hsupp
  have hrp := Nat.pos_of_mem_divisors hr
  have hrr : (0:ℝ) < r := by exact_mod_cast hrp
  have hE := coefficientEnergy_nonneg S a
  have hrows : ∀ v ∈ binarySquarefreeRows K j, Odd v ∧ ((2^j:ℕ):ℝ) ≤ v := by
    intro v hv
    obtain ⟨hv',hlo,hhi⟩ := Finset.mem_filter.mp hv
    exact ⟨(mem_oddSquarefreeUpTo.mp hv').2.2.1,by exact_mod_cast hlo⟩
  by_cases hactive : ∃ v ∈ binarySquarefreeRows K j, g v ≠ 0
  · obtain ⟨v,hv,hnz⟩ := hactive
    have ht := complement_boundary_transition hT hΔ hr hv (hsupp v hv hnz)
    have hsum := hbound (binarySquarefreeRows K j) S a N hN (fun v hv => (hrows v hv).1) hS
    calc
      _ ≤ ∑ v ∈ binarySquarefreeRows K j,
          ‖(μ r:ℂ)*(μ 1:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*1):ℝ):ℂ)*g v*
            coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (v:ℤ)‖ := norm_sum_le _ _
      _ ≤ ∑ v ∈ binarySquarefreeRows K j,
          (A*Real.sqrt (M/(2^j:ℕ))/(r:ℝ))*
            ‖coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (v:ℤ)‖ := by
        apply Finset.sum_le_sum
        intro v hv
        rw [norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [Nat.cast_one,mul_one] using complement_weight_norm_le (g v) hM
          (by positivity : (0:ℝ)<(2^j:ℕ)) hrp (by norm_num : 0<1) (le_refl 1)
          (hrows v hv).2 hA (hg v hv)
      _ = (A*Real.sqrt (M/(2^j:ℕ))/(r:ℝ))*
          ∑ v ∈ binarySquarefreeRows K j,
            ‖coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (v:ℤ)‖ := by rw [Finset.mul_sum]
      _ ≤ (A*Real.sqrt (M/(2^j:ℕ))/(r:ℝ))*(C*(N:ℝ)^ε*(H*(x+N))*coefficientEnergy S a) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hsum.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnorm (by positivity)) hE)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left ht
          (show 0 ≤ (A*C*H/(r:ℝ))*(N:ℝ)^ε*coefficientEnergy S a*(N:ℝ) by positivity)
        have hsame := add_le_add (le_refl ((A*C*H/(r:ℝ))*(N:ℝ)^ε*
          coefficientEnergy S a*Real.sqrt (M/(2^j:ℕ))*x)) hh
        convert hsame using 1 <;> ring
  · have hz : ∀ v ∈ binarySquarefreeRows K j, g v = 0 := by
      intro v hv
      by_contra hnz
      exact hactive ⟨v,hv,hnz⟩
    have hsum : (∑ v ∈ binarySquarefreeRows K j,
        (μ r:ℂ)*(μ 1:ℂ)*((Real.sqrt (M/v)/((r:ℝ)*1):ℝ):ℂ)*g v*
          coprimeProductDivisorJacobiRow S S a (fun n => conj (a n)) 1 (v:ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      rw [hz v hv]
      ring
    rw [hsum,norm_zero]
    positivity

end Ostmann.QuadraticSieve

end

end OAI
