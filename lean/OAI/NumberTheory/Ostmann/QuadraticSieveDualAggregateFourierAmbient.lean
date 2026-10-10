import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateFourierGrowth
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateFourierRaw
import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateFourierWeights

namespace OAI

namespace Ostmann.QuadraticSieve
open ComplexConjugate
open scoped SchwartzMap FourierTransform

theorem dual_fourier_kernel_aggregate_ambient (W : 𝓢(ℝ,ℂ)) {ξ : ℝ}
    (hξ1 : 1 < ξ) (hξ2 : ξ ≤ 2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ ε/100 →
      ∀ (P M H T A : ℝ) (K Δ N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) (g : ℕ → ℕ → ℕ → ℂ),
      1 ≤ P → 1 ≤ M → M ≤ P → 0 < H → 0 ≤ A → 0 < K → 0 < Δ → 0 < N →
      (N : ℝ) ≤ P → (K : ℝ) ≤ P^3 → T = P^η → (N : ℝ) ≤ 2*H →
      S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H ≤ (n : ℝ)) →
      (∀ e ∈ (2*Δ).divisors, ∀ d, ∀ v ∈ oddSquarefreeUpTo K, ‖g e d v‖ ≤ A) →
      (∀ e ∈ (2*Δ).divisors, ∀ d, ∀ v ∈ oddSquarefreeUpTo K, g e d v ≠ 0 →
        dualWindowLower M H T e v < (d : ℝ)) →
      ‖dualAggregateFourierSum W M T K Δ N S a g‖ ≤
        C*A*P^ε*(Δ : ℝ)^2*(M+Real.sqrt M*(K : ℝ)^(ξ-1/2))*coefficientEnergy S a := by
  let δ : ℝ := ε/100
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Cr,hCr,hraw⟩ := dual_fourier_raw_sum_bound W hξ1 hξ2 hξ δ δ hδ hδ
  obtain ⟨Cg,hCg,hgrowth⟩ := dual_fourier_depth_loss ε hε
  refine ⟨Cr*Cg,by positivity,?_⟩
  intro η hη hηδ P M H T A K Δ N S a g hP hM hMP hH hA hK hΔ hN hNP hKP hT hNH hS hSH hg hsupp
  have hMp : 0 < M := by linarith
  have hT1 : 1 ≤ T := by rw [hT]; exact Real.one_le_rpow hP hη.le
  have hE := coefficientEnergy_nonneg S a
  have hr := hraw P M H T A K Δ N S a g hP hMp hMP hH hT1 hA hK hΔ hN hNP hKP hNH hS hSH hg hsupp
  have hloss := hgrowth η P T K N hη hηδ hP hT hK hN hNP hKP
  have hh := mul_le_mul_of_nonneg_left hloss
    (show 0 ≤ Cr*A*(Δ : ℝ)*(M+Real.sqrt M*(K : ℝ)^(ξ-1/2))*coefficientEnergy S a by positivity)
  have hΔ1 : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hΔsq : (Δ : ℝ) ≤ (Δ : ℝ)^2 := by nlinarith
  calc
    _ ≤ _ := hr
    _ ≤ (Cr*Cg)*A*P^ε*(Δ : ℝ)*(M+Real.sqrt M*(K : ℝ)^(ξ-1/2))*coefficientEnergy S a := by
      convert hh using 1 <;> (try dsimp [δ]) <;> ring
    _ ≤ _ := by gcongr

theorem dualCorrelationFourierCorrection_eq_actual_kernel (W : 𝓢(ℝ,ℂ))
    (M H T : ℝ) (hM : 0 < M) (K Δ N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    dualCorrelationFourierCorrection W M Δ K S a (dualWindowLower M H T) (dualWindowUpper M H T)
      (fun _ _ => 16*T^2) =
      (1/2 : ℂ)*dualAggregateFourierSum W M T K Δ N S a (dualAggregateFourierScalar M H T) := by
  rw [dualCorrelationFourierCorrection_eq_rows W M hM Δ K N S a _ _ _ hS]
  simp_rw [dualFourierDivisorRows_eq_actual_scalar,←Finset.mul_sum]
  unfold dualAggregateFourierSum
  refine congrArg (fun value : ℂ => (1/2 : ℂ)*value) ?_
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro s hs
  exact Finset.sum_comm

theorem dual_fourier_correction_aggregate_ambient (W : 𝓢(ℝ,ℂ)) {ξ : ℝ}
    (hξ1 : 1 < ξ) (hξ2 : ξ ≤ 2)
    (hξ : ExponentBound (fun M N => quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N)) ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ ε/100 →
      ∀ (P M H T : ℝ) (K Δ N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ),
      1 ≤ P → 1 ≤ M → M ≤ P → 0 < H → 0 < K → 0 < Δ → 0 < N →
      (N : ℝ) ≤ P → (K : ℝ) ≤ P^3 → T = P^η → (N : ℝ) ≤ 2*H →
      S ⊆ oddSquarefreeUpTo N → (∀ n ∈ S, H ≤ (n : ℝ)) →
      ‖dualCorrelationFourierCorrection W M Δ K S a (dualWindowLower M H T) (dualWindowUpper M H T)
        (fun _ _ => 16*T^2)‖ ≤
        C*P^ε*(Δ : ℝ)^2*(M+Real.sqrt M*(K : ℝ)^(ξ-1/2))*coefficientEnergy S a := by
  obtain ⟨C,hC,hbound⟩ := dual_fourier_kernel_aggregate_ambient W hξ1 hξ2 hξ ε hε
  refine ⟨C,hC,?_⟩
  intro η hη hηδ P M H T K Δ N S a hP hM hMP hH hK hΔ hN hNP hKP hT hNH hS hSH
  have hh := hbound η hη hηδ P M H T 1 K Δ N S a (dualAggregateFourierScalar M H T)
    hP hM hMP hH (by norm_num) hK hΔ hN hNP hKP hT hNH hS hSH
    (fun e he d v hv => dualAggregateFourierScalar_norm_le M H T e d v)
    (fun e he d v hv hnz => dualAggregateFourierScalar_support hnz)
  rw [dualCorrelationFourierCorrection_eq_actual_kernel W M H T (by linarith) K Δ N S a
    (fun n hn => ⟨(mem_oddSquarefreeUpTo.mp (hS hn)).1,(mem_oddSquarefreeUpTo.mp (hS hn)).2.1⟩),norm_mul]
  have hhalf : ‖(1/2 : ℂ)‖ ≤ 1 := by norm_num
  exact (mul_le_of_le_one_left (norm_nonneg _) hhalf).trans (by simpa only [mul_one] using hh)

end Ostmann.QuadraticSieve

end OAI
