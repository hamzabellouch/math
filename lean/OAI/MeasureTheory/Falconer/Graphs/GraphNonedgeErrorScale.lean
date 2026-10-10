import OAI.MeasureTheory.Falconer.Graphs.GraphNonedgeGradient

namespace OAI

namespace PlanarFalconer

theorem graph_representative_error_small {sig C : ℝ} (hsig : 0 < sig) (_hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p θ ℓ : ℝ, 0 ≤ θ → 0 ≤ ℓ →
      θ ≤ graphUncappedAngularScale N sig (p-a) → ℓ ≤ C*(2:ℝ)^(-a) →
      20*(2:ℝ)^(-p)+θ*ℓ ≤ ((2:ℝ)^(-p)*((2:ℝ)^N)^(30*sig))/2 := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by positivity : 0 < 20*sig) (2*(20+C))
  refine ⟨N₀,?_⟩
  intro N hN a p θ ℓ _hθ hℓ hθbound hℓbound
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRpos : 0 < R := by positivity
  have h10 : 1 ≤ R^(10*sig) := Real.one_le_rpow hR (by positivity)
  have hpow : R^(30*sig) = R^(20*sig)*R^(10*sig) := by
    rw [← Real.rpow_add hRpos]
    congr 1
    ring
  have he : graphUncappedAngularScale N sig (p-a)*(C*(2:ℝ)^(-a)) = C*(2:ℝ)^(-p)*R^(10*sig) := by
    dsimp [graphUncappedAngularScale,R]
    calc
      _ = C*((2:ℝ)^(-(p-a))*(2:ℝ)^(-a))*((2:ℝ)^N)^(10*sig) := by ring
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
        congr 3
        ring
  have hprod := mul_le_mul hθbound hℓbound hℓ (graphUncappedAngularScale_pos N sig (p-a)).le
  rw [he] at hprod
  have hconst : 2*(20+C) ≤ R^(20*sig) := hN₀ N hN
  have hgain := mul_le_mul_of_nonneg_right hconst (by positivity : 0 ≤ (2:ℝ)^(-p)*R^(10*sig))
  have hone := mul_le_mul_of_nonneg_left h10 (by positivity : 0 ≤ (2:ℝ)^(-p))
  change _ ≤ ((2:ℝ)^(-p)*R^(30*sig))/2
  rw [hpow]
  nlinarith

end PlanarFalconer

end OAI
