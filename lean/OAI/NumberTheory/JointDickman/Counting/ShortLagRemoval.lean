import OAI.NumberTheory.JointDickman.Counting.ShortLagSet

namespace OAI

/-! # Short additive lags have a uniformly small total contribution -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem arithmetic_short_lags_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ H : ℕ, H ≤ auxiliaryCutoff B → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ τ C : ℝ, ∀ F : ℕ → ℂ,
      (∀ n, ‖F n‖ ≤ 2) →
      |∑ j ∈ nonzeroShortLags H, kernelLagCorrelation B L τ C T N j F| ≤
        K*(H : ℝ)/(T : ℝ)+ε := by
  obtain ⟨K,hK,hbound⟩ := finite_kernelLagCorrelation_bound hFord hM
  refine ⟨8*K*Real.exp 24, by positivity, ?_⟩
  filter_upwards [hbound] with B hB
  intro T hT hTs H hH ε hε
  have hJ : ∀ j ∈ nonzeroShortLags H, j ≠ 0 ∧ j.natAbs ≤ auxiliaryCutoff B := by
    intro j hj
    have h := mem_nonzeroShortLags.mp hj
    exact ⟨h.1,h.2.trans hH⟩
  filter_upwards [hB T hT hTs (nonzeroShortLags H) hJ ε hε] with N hN
  intro L τ C F hF
  apply (hN L τ C F hF).trans
  have h := mul_le_mul_of_nonneg_left (shortLag_singular_sum H)
    (show 0 ≤ 4*K/(T : ℝ) by positivity)
  have he : (4*K/(T : ℝ))*((2*Real.exp 24)*(H : ℝ)) =
      (8*K*Real.exp 24)*(H : ℝ)/(T : ℝ) := by ring
  rw [he] at h
  linarith only [h]

theorem graph_energy_eq_lag_correlations (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (F : ℕ → ℂ) :
    arithmeticOffDiagonalGraph B L τ C T N F/((B : ℝ)*T) =
      ∑ j ∈ Icc (-(T : ℤ)) T, kernelLagCorrelation B L τ C T N j F := by
  rw [arithmeticOffDiagonalGraph_kernel, sum_comm]
  unfold kernelLagCorrelation
  rw [← sum_div]
  ring

noncomputable def graphEnergyWithoutShortLags (B L : ℕ) (τ C : ℝ)
    (T N H : ℕ) (F : ℕ → ℂ) : ℝ :=
  ∑ j ∈ Icc (-(T : ℤ)) T\nonzeroShortLags H, kernelLagCorrelation B L τ C T N j F

theorem graph_short_lag_removal_identity (B L : ℕ) (τ C : ℝ)
    (T N H : ℕ) (hH : H ≤ T) (F : ℕ → ℂ) :
    arithmeticOffDiagonalGraph B L τ C T N F/((B : ℝ)*T) -
      graphEnergyWithoutShortLags B L τ C T N H F =
        ∑ j ∈ nonzeroShortLags H, kernelLagCorrelation B L τ C T N j F := by
  have hsub : nonzeroShortLags H ⊆ Icc (-(T : ℤ)) T := by
    intro j hj
    have hh := (mem_nonzeroShortLags.mp hj).2.trans hH
    have hab : |j| ≤ (T : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hh
    exact mem_Icc.mpr (abs_le.mp hab)
  have hs := sum_sdiff hsub (f := fun j => kernelLagCorrelation B L τ C T N j F)
  rw [graph_energy_eq_lag_correlations]
  unfold graphEnergyWithoutShortLags
  linarith

theorem arithmetic_short_lags_removable
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ T : ℕ,
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ H : ℕ, H ≤ T → H ≤ auxiliaryCutoff B → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, ∀ τ C : ℝ, ∀ F : ℕ → ℂ,
      (∀ n, ‖F n‖ ≤ 2) →
      |arithmeticOffDiagonalGraph B L τ C T N F/((B : ℝ)*T) -
        graphEnergyWithoutShortLags B L τ C T N H F| ≤ K*(H : ℝ)/(T : ℝ)+ε := by
  obtain ⟨K,hK,hbound⟩ := arithmetic_short_lags_bound hFord hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound] with B hB
  intro T hT hTs H hHT hHB ε hε
  filter_upwards [hB T hT hTs H hHB ε hε] with N hN
  intro L τ C F hF
  rw [graph_short_lag_removal_identity B L τ C T N H hHT F]
  exact hN L τ C F hF

end JointDickman

end OAI
