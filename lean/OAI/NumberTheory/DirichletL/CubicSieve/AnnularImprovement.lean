import OAI.NumberTheory.DirichletL.CubicSieve.CostGrowth
import OAI.NumberTheory.DirichletL.CubicSieve.ColumnShells

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge CanonicalQuadraticSieve
open IdealMobiusDivisorSum SecondPassArithmetic EisensteinSchwartzPoisson
open SevenEighths.CubicDyadicDecay
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem HasCubicExponent.annular_improved {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2)
    (θ : ℝ) (hθ : 0 < θ) (hθsmall : θ < 1/2) :
    ∃ K : ℝ, 0 < K ∧ ∀ {n : Type} [Fintype n] [DecidableEq n]
      (M N : ℝ), 1 ≤ M → 1 ≤ N → ∀ (cols : n → Ideal O), Function.Injective cols →
      (∀ j, Admissible (cols j)) →
      (∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
      ∀ (a : n → ℂ) (R : Finset O),
        (∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M) →
        (∑ z ∈ R, ‖∑ j, cubicRow (cols j) z*a j‖^2) ≤
          K*N^(6*θ)*(M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1))*∑ j, ‖a j‖^2 := by
  obtain ⟨C,hC,hcf⟩ := cubic_common_factor_frequency_bound
  obtain ⟨A,hA,hfb⟩ := h.frequencyCost_bound hξ hξ2 θ hθ hθsmall
  let Z := ‖paperRadialFourier rowMajorant 0‖
  let P := decayConstant (1/3+θ)
  let Q := decayConstant (ξ+θ)
  let H := 2*C*IdealCoprimeSieveOperator.supportConstant θ hθ*A
  let V := 1+2*Z+H*(P+Q)
  let Dv := DivisorBlockCauchy.divisorConstant θ hθ
  have hZ : 0 ≤ Z := norm_nonneg _
  have hP : 0 ≤ P := (decayConstant_pos _ (by linarith) (by linarith)).le
  have hQ : 0 ≤ Q := (decayConstant_pos _ (by linarith) (by linarith)).le
  have hH : 0 ≤ H := by
    dsimp [H]
    have hs := (IdealCoprimeSieveOperator.supportConstant_pos θ hθ).le
    positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hDv : 0 < Dv := DivisorBlockCauchy.divisorConstant_pos θ hθ
  refine ⟨V*Dv^2, by positivity, ?_⟩
  intro n _ _ M N hM hN cols hinj hc hcols a R hR
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let S := M+(M*N)^(2/3 : ℝ)+M^(1-ξ)*N^(2*ξ-1)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let U := V*N^(4*θ)*S
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hcost (D : Ideal O) (hD : D ∈ gcdPool cols) (E : Ideal O) (hE : E ∈ idealDivisors D) :
      frequencyCost C θ hθ (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ)) ≤ U := by
    have hc0 (j : n) : cols j ≠ 0 := primaryGenerator_ne_zero_ideal _ (hc j).2
    have hD0 := gcdPool_ne_zero cols hc0 D hD
    have hDE := (mem_idealDivisors hD0).mp hE
    have hE0 : E ≠ 0 := ne_zero_of_dvd_ne_zero hD0 hDE
    have he1 : 1 ≤ (Ideal.absNorm E : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hE0)
    have hed : (Ideal.absNorm E : ℝ) ≤ (Ideal.absNorm D : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD0))
        (map_dvd Ideal.absNorm hDE)
    have hdN := (columnDivisorPool_norm_bounds cols hc0 N (fun j => (hcols j).2) D
      (gcdPool_subset_columnDivisorPool cols hc0 hD)).2
    have hd0 : 0 < (Ideal.absNorm D : ℝ) := by linarith
    have he0 : 0 < (Ideal.absNorm E : ℝ) := by linarith
    have hh := hfb C θ hC hθ (M/(Ideal.absNorm E : ℝ)) (N/(Ideal.absNorm D : ℝ))
      (div_pos hM0 he0) ((one_le_div hd0).mpr hdN)
    have hd := frequencyCost_descendant_of_bound C θ A θ ξ M N
      (Ideal.absNorm D) (Ideal.absNorm E) hC hθ hA.le hθ.le (by linarith)
      (by linarith) (by linarith) hM0 hN0 he1 hed hdN hh
    have hb := poisson_envelope_absorb M N θ θ ξ H Z P Q hM hN hθ.le hθ.le hH hZ hP hQ
    have hx : 3*θ+θ = 4*θ := by ring
    rw [hx] at hb
    apply (hd.trans hb).trans
    change (2*Z+H*(P+Q))*N^(4*θ)*S ≤ V*N^(4*θ)*S
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp [V]; linarith) (Real.rpow_nonneg hN0.le _)) hS
  have henergy := (hcf θ hθ M N hM0 cols hinj hc hcols a R hR).trans
    (common_factor_uniform_cost C θ U M N hθ hU hN0.le cols hc (fun j => (hcols j).2) a hcost)
  have hp : N^(4*θ)*(N^θ)^2 = N^(6*θ) := by
    rw [← Real.rpow_mul_natCast hN0.le, ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  calc
    _ ≤ U*(Dv*N^θ)^2*∑ j, ‖a j‖^2 := henergy
    _ = (V*Dv^2)*(N^(4*θ)*(N^θ)^2)*S*∑ j, ‖a j‖^2 := by dsimp [U]; ring
    _ = _ := by rw [hp]

end
end SevenEighths.CubicSieve

end OAI
