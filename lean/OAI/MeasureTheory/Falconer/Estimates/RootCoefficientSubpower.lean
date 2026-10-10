import OAI.MeasureTheory.Falconer.Estimates.RootLeibnizBounds
import OAI.MeasureTheory.Falconer.Shells.HighShellSubpower

namespace OAI

namespace PlanarFalconer

theorem uniform_root_inverseLeibniz_subpower {eps : ℝ} (heps : 0 < eps) (j : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
      d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    ((inverseLeibnizTerms j (rootMaskIndices d e)).map
      (fun b => ‖b.1‖)).sum * (2:ℝ)^j ≤ ((2:ℝ)^N)^eps := by
  let C := (inverseStationaryExpr j).cost * (4:ℝ)^(2*j) * (2:ℝ)^j
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos heps) C
  obtain ⟨N₂,h₂⟩ := fixed_polynomial_subpower (6*j) (half_pos heps)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN d e hd he
  have hpoly : (((N:ℝ)+1)^3)^(2*j) = ((N:ℝ)+1)^(6*j) := by
    rw [← pow_mul]
    congr 1
    omega
  have hbound := mul_le_mul_of_nonneg_right (root_inverseLeibniz_cost d e N j hd he)
    (by positivity : 0 ≤ (2:ℝ)^j)
  apply hbound.trans
  calc
    _ = C*((N:ℝ)+1)^(6*j) := by rw [mul_pow,hpoly]; dsimp [C]; ring
    _ ≤ C*(4*(N:ℝ)+1)^(6*j) := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by have := Nat.cast_nonneg (α := ℝ) N; linarith) _)
      (by dsimp [C]; exact mul_nonneg (mul_nonneg (inverseStationaryExpr j).cost_nonneg (by positivity)) (by positivity))
    _ ≤ ((2:ℝ)^N)^(eps/2)*((2:ℝ)^N)^(eps/2) :=
      mul_le_mul (h₁ N ((le_max_left _ _).trans hN)) (h₂ N ((le_max_right _ _).trans hN))
        (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end PlanarFalconer

end OAI
