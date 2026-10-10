import OAI.NumberTheory.Ostmann.QuadraticSieveComplementAggregateGrowth
import OAI.NumberTheory.Ostmann.QuadraticSieveComplementAggregateRaw

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

theorem complement_kernel_power_bound_ambient {ξ : ℝ} (hξ1 : 1 ≤ ξ) (hξ2 : ξ ≤ 2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ ε/16 → ∀ (P M T A₀ : ℝ) (K Δ N : ℕ)
      (S : Finset ℕ) (a : ℕ → ℂ) (g : ℕ → ℕ → ℕ → ℂ),
      1 ≤ P → 1 ≤ M → (N:ℝ) ≤ P → 0 ≤ A₀ → 0 < K → 0 < Δ → 0 < N →
      (K:ℝ) ≤ P^3 → T = P^η →
      S ⊆ oddSquarefreeUpTo N →
      (∀ r ∈ (2*Δ).divisors, ∀ d, ∀ v ∈ oddSquarefreeUpTo K, ‖g r d v‖ ≤ A₀*T^2) →
      (∀ r ∈ (2*Δ).divisors, ∀ d, ∀ v ∈ oddSquarefreeUpTo K, g r d v ≠ 0 →
        complementWindowLower M T v < (r*d:ℕ)) →
      ‖complementKernelSum M K Δ N S a g‖ ≤
        C*A₀*P^ε*(Δ:ℝ)^2*
          ((N:ℝ)+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a := by
  let δ : ℝ := ε/16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Cr,hCr,hraw⟩ := complement_raw_sum_bound hξ1 hξ2 hξ δ hδ
  obtain ⟨Cg,hCg,hgrowth⟩ := complement_aggregate_growth δ hδ
  refine ⟨Cr*Cg,by positivity,?_⟩
  intro η hη hηδ P M T A₀ K Δ N S a g hP hM hNP hA hK hΔ hN hKbound hT hS hg hsupp
  have hT1 : 1 ≤ T := by rw [hT]; exact Real.one_le_rpow hP hη.le
  have he := hgrowth P K N hP hK hN hNP hKbound
  have hp : P^(13*δ) ≤ P^ε := Real.rpow_le_rpow_of_exponent_le hP (by dsimp [δ]; linarith)
  have hTs : T ≤ P^δ := by
    rw [hT]
    exact Real.rpow_le_rpow_of_exponent_le hP hηδ
  have hTc : T^3 ≤ (P^δ)^3 := pow_le_pow_left₀ (by linarith) hTs 3
  have heT : ((Nat.log 2 K+1:ℕ):ℝ)*((Nat.log 2 (N^2)+2:ℕ):ℝ)*
      ((2:ℝ)*K*N)^δ*(N:ℝ)^δ*T^3 ≤ Cg*P^(13*δ) := by
    calc
      _ ≤ ((Nat.log 2 K+1:ℕ):ℝ)*((Nat.log 2 (N^2)+2:ℕ):ℝ)*
          ((2:ℝ)*K*N)^δ*(N:ℝ)^δ*(P^δ)^3 :=
        mul_le_mul_of_nonneg_left hTc (by positivity)
      _ ≤ _ := he
  have he' := heT.trans (mul_le_mul_of_nonneg_left hp hCg.le)
  have hr := hraw M T (A₀*T^2) K Δ N S a g (by linarith) hT1 (by positivity)
    hK hΔ hN hS hg hsupp
  have hE := coefficientEnergy_nonneg S a
  have hh := mul_le_mul_of_nonneg_left he'
    (show 0 ≤ Cr*A₀*(Δ:ℝ)^2*((N:ℝ)+Real.sqrt M*(K:ℝ)^(ξ-1/2))*coefficientEnergy S a by positivity)
  refine hr.trans ?_
  convert hh using 1 <;> ring

end Ostmann.QuadraticSieve

end

end OAI
