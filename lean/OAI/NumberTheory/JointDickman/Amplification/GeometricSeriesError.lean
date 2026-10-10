import OAI.NumberTheory.JointDickman.Probability.GeometricKernelIdentity
import OAI.NumberTheory.JointDickman.Probability.SampledLogKernelBound

namespace OAI

/-! # The box-summed singular-series truncation error -/

namespace JointDickman
open Finset Filter
open scoped Topology SchwartzMap

theorem geometric_singularSeries_error
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {t L U : ℝ} (ht : 0 < t) (hLU : L ≤ U)
    (w₁ w₂ : ℝ → ℝ) (w : 𝓢(ℝ,ℝ))
    {M₁ M₂ : ℝ} (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hw₁ : ∀ x, |w₁ x| ≤ M₁) (hw₂ : ∀ x, |w₂ x| ≤ M₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ j : ℕ, [NeZero j] → ∀ Q : ℕ, j*Q ≤ auxiliaryCutoff B →
      ∀ S : Finset ℤ, ∀ β D : ℝ, 0 ≤ D → ∀ d : ℤ → ℝ,
      (∀ k ∈ S, |d k| ≤ D) → ∀ g h : (auxiliaryPrimes B → Bool) → ℝ,
      (∀ x, |g x| ≤ 1) → (∀ x, |h x| ≤ 1) →
      ‖((B : ℂ)/j)*∑ k ∈ S, (d k : ℂ)*
        (sampledEndpointKernel m B j Q (geometricHistogramWindow m B t L U k)
          g h w₁ w₂ (Real.exp ((k : ℝ)*t)) β w-
        (singularSeries j : ℂ)*sampledEndpointLogKernel m B (geometricHistogramWindow m B t L U k)
          g h w₁ w₂ (Real.exp ((k : ℝ)*t)) β w)‖ ≤
        (D*C)*(((j : ℝ)/j.totient)/j)*singularSeriesTail (Q+1) := by
  obtain ⟨C,hC,he⟩ := geometric_sampled_log_kernel_bound hSD hSW hM hMP ht hLU
    w₁ w₂ w hM₁ hM₂ hw₁ hw₂
  refine ⟨C,hC,?_⟩
  intro m hm
  filter_upwards [he m hm,eventually_ge_atTop 1] with B heB hB
  intro j _ Q hcut S β D hD d hd g h hg hh
  have hBpos : 0 < B := by omega
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  let E := fun k => sampledEndpointKernel m B j Q (geometricHistogramWindow m B t L U k)
      g h w₁ w₂ (Real.exp ((k : ℝ)*t)) β w-
    (singularSeries j : ℂ)*sampledEndpointLogKernel m B (geometricHistogramWindow m B t L U k)
      g h w₁ w₂ (Real.exp ((k : ℝ)*t)) β w
  let A := ((j : ℝ)/j.totient)*singularSeriesTail (Q+1)
  have hA : 0 ≤ A := mul_nonneg (by positivity) (singularSeriesTail_nonneg _)
  have hsum : (∑ k ∈ S, ‖(d k : ℂ)*E k‖) ≤ D*A*(C/B) := by
    calc
      _ ≤ ∑ k ∈ S, D*A*‖sampledEndpointLogKernel m B (geometricHistogramWindow m B t L U k)
          g h w₁ w₂ (Real.exp ((k : ℝ)*t)) β w‖ := by
        apply sum_le_sum
        intro k hk
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact (mul_le_mul (hd k hk)
          (sampledEndpointKernel_singularSeries_error hMP hm hBpos hcut _ g h w₁ w₂ _ β w)
          (norm_nonneg _) hD).trans_eq (by ring)
      _ = D*A*(∑ k ∈ S, ‖sampledEndpointLogKernel m B (geometricHistogramWindow m B t L U k)
          g h w₁ w₂ (Real.exp ((k : ℝ)*t)) β w‖) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (heB S β g h hg hh) (mul_nonneg hD hA)
  change ‖((B : ℂ)/j)*∑ k ∈ S, (d k : ℂ)*E k‖ ≤ _
  rw [norm_mul,norm_div,Complex.norm_natCast,Complex.norm_natCast]
  calc
    _ ≤ ((B : ℝ)/j)*(D*A*(C/B)) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans hsum) (by positivity)
    _ = _ := by dsimp [A]; field_simp

end JointDickman

end OAI
