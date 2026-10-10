import OAI.MeasureTheory.Falconer.Recursion.FrostmanProfiles

namespace OAI

/-! # One regularization choice for all measures with the fixed Frostman bound -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem uniform_frostman_profile_envelope (hd : 0 < d) (Q : DyadicCube d) (hQ : 0 < Q.side)
    {s C lam : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam) :
    ∃ H N₀ : ℕ, 0 < H ∧
      (∀ N ≥ N₀, 0 < N ∧ 0 < N/H ∧ N/(N/H)+1 ≤ 2*H ∧
        ((N/H:ℕ):ℝ) ≤ lam*(N:ℝ) ∧ (2:ℝ)^(N/(N/H)+2) ≤ ((2:ℝ)^N)^lam) ∧
      ∀ N ≥ N₀, ∀ (μ : Measure (Space d)) [IsProbabilityMeasure μ],
      (∀ x : Space d, ∀ r > 0, μ (Metric.ball x r) ≤ ENNReal.ofReal (C*r^s)) →
      ∀ p ∈ regularizationLeaves Q μ N,
        regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H)
          (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) →
        ∀ j ≤ N, s*(j:ℝ)/(N:ℝ)-((d:ℝ)+3)*lam ≤ sourceProfile Q μ N (N/H) p j := by
  obtain ⟨H,N₁,hH,hscales⟩ := PlanarFalconer.exists_regularization_block_control hlam
  obtain ⟨N₂,hconst⟩ := fixed_constant_absorbed hlam (C*(2*Real.sqrt d*Q.side)^s)
  refine ⟨H,max N₁ N₂,hH,fun N hN => hscales N ((le_max_left _ _).trans hN),?_⟩
  intro N hN μ _ hball p hp hret j hj
  have hs := hscales N ((le_max_left _ _).trans hN)
  apply sourceProfile_frostman_lower Q hQ μ hs.1 hs.2.1 hs.2.2.2.1 hs.2.2.2.2 hp
    (retained_label_real_mass_lower Q μ hret) _ hj
  intro k hk P hP
  have hh := dyadic_cell_frostman_profile_bound hd Q hQ μ hC hball hs.1 P
  rw [hP] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (hconst N ((le_max_right _ _).trans hN)) (by positivity))

end Falconer.Regularization

end OAI
