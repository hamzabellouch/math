import OAI.MeasureTheory.Falconer.Angular.InverseStationaryWeighted
import OAI.MeasureTheory.Falconer.Angular.InverseStationaryTriangle

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff Topology

noncomputable def inverseCircleIntegral (n : ℕ) (Λ : ℝ) (ψ f : ℝ → ℂ) : ℂ :=
  ((Λ^(1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1), ((Λ⁻¹:ℝ):ℂ)^j *
    ∫ θ in (-Real.pi)..Real.pi,
      cosineOscillator Λ θ * (ψ θ * inverseStationaryOperator j f θ)

theorem inverseCircleIntegral_weighted (n : ℕ) (Λ : ℝ) (ψ f : ℝ → ℂ) :
    inverseCircleIntegral n Λ ψ f =
      ∑ j ∈ Finset.range (n+1), (inverseStationaryWeight Λ j:ℂ) *
        ∫ θ in (-Real.pi)..Real.pi,
          cosineOscillator Λ θ * (ψ θ * inverseStationaryOperator j f θ) := by
  simp [inverseCircleIntegral, inverseStationaryWeight, Finset.mul_sum, mul_assoc]

theorem weighted_inverse_expansions_cancel (n : ℕ) {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    (∑ j ∈ Finset.range (n+1), (inverseStationaryWeight Λ j:ℂ) *
      inverseDirectExpansion (n-j) j Λ f) = Complex.exp (Complex.I*(Λ:ℂ))*f 0 := by
  have hhalf : ((Λ^(1/2:ℝ):ℝ):ℂ)*((Λ^(-1/2:ℝ):ℝ):ℂ) = 1 := by
    exact_mod_cast stationary_half_cancel hΛ
  conv_rhs => rw [← inverseStationaryOperator_triangle_reverse n ((Λ⁻¹:ℝ):ℂ) hf 0]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have he : n-j+1 = n+1-j := by omega
  simp only [inverseStationaryWeight, Complex.ofReal_mul, Complex.ofReal_pow,
    inverseDirectExpansion, he]
  calc
    _ = Complex.exp (Complex.I*(Λ:ℂ)) *
        (((Λ^(1/2:ℝ):ℝ):ℂ)*((Λ^(-1/2:ℝ):ℝ):ℂ)) *
          (((Λ⁻¹:ℝ):ℂ)^j * ∑ h ∈ Finset.range (n+1-j),
            ((Λ⁻¹:ℝ):ℂ)^h * directStationaryOperator h (inverseStationaryOperator j f) 0) := by ring
    _ = _ := by simp only [hhalf, mul_one, Finset.mul_sum, pow_add, mul_assoc]

theorem inverse_circle_ratio_remainder (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧
    ∀ {ψ f : ℝ → ℂ}, ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ f →
    Function.Periodic ψ (2*Real.pi) → Function.Periodic f (2*Real.pi) →
    ψ =ᶠ[𝓝 0] (fun _ => 1) → ψ =ᶠ[𝓝 Real.pi] (fun _ => 0) →
    ∀ {P C D Λ : ℝ}, 0 ≤ P → 0 ≤ C → 1 ≤ D → 1 ≤ Λ → D^2/Λ ≤ 1 →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k ψ x‖ ≤ P) →
    (∀ k ≤ 4*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖inverseCircleIntegral n Λ ψ f - Complex.exp (Complex.I*(Λ:ℂ))*f 0‖ ≤
      A*P*C*D^2*(D^2/Λ)^(n+1) := by
  choose A hA hbound using fun j : ℕ =>
    cutoff_inverse_weighted_remainder n (min j n) (min_le_right _ _)
  refine ⟨∑ j ∈ Finset.range (n+1), A j, Finset.sum_nonneg (fun j _ => hA j), ?_⟩
  intro ψ f hψ hf hpψ hpf hψ₀ hψπ P C D Λ hP hC hD hΛ hr hbψ hbf
  rw [inverseCircleIntegral_weighted,
    ← weighted_inverse_expansions_cancel n (zero_lt_one.trans_le hΛ) hf,
    ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), A j*P*C*D^2*(D^2/Λ)^(n+1) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      simpa only [min_eq_left hj'] using
        hbound j hψ hf hpψ hpf hψ₀ hψπ hP hC hD hΛ hr hbψ hbf
    _ = _ := by simp only [Finset.sum_mul]

end PlanarFalconer

end OAI
