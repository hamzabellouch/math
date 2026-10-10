import OAI.MeasureTheory.Falconer.Graphs.ProfileGraphBudget
import OAI.MeasureTheory.Falconer.Graphs.GraphEnergyError
import OAI.MeasureTheory.Falconer.Graphs.DyadicRowCount

namespace OAI

/-! # Arbitrary-power error for the normalized profile graph estimate -/

namespace Falconer
open MeasureTheory

theorem profile_graph_error_arbitrary_power (d : ℕ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ) (minOrder : ℕ := 0) :
    ∃ k : ℕ, minOrder ≤ k ∧ ∀ {A C W H B : ℝ},
      0 ≤ A → 0 ≤ C → 0 ≤ W → 0 ≤ H → 0 ≤ B →
      ∀ (Q₁ Q₂ : DyadicCube d) (ρ₁ ρ₂ : Measure (Space d))
        (m₁ m₂ : ℝ → ℝ) (N a p : ℕ), 0 < N → a ≤ p → p ≤ N →
      m₁ ((a:ℝ)/N) ≤ d → m₂ ((a:ℝ)/N) ≤ d →
      ∀ {D v τ Cap Z : ℝ} {K : ℕ},
      0 ≤ D → v ≤ N → 0 < τ → 0 ≤ Cap → 0 ≤ Z →
      (K:ℝ) ≤ Cap*((2:ℝ)^N)^d →
      16*D/((2:ℝ)^v*τ) ≤ Z*((2:ℝ)^N)^(-(26*σ)) →
      (2:ℝ)^((d:ℝ)*(v-a)) *
        ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
          (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        capGraphError d k A C W ((2:ℝ)^N) (T+(11*d:ℕ))
          (profileModelMass m₁ N p) (profileModelMass m₂ N p) H B D v τ K
          (Q₁.occupiedPaths ρ₁ (p-a) ×ˢ Q₂.occupiedPaths ρ₂ (p-a)).card ≤
      Cap^2 *
        ((A*(4^k*H*B*B)*(B*B)*(sphereMeasure d).real Set.univ*(4*W))*Z^k +
          (B*B)*(B*B)*C*((sphereMeasure d).real Set.univ)^2) * ((2:ℝ)^N)^(-T) := by
  obtain ⟨k,hmin,hk⟩ := capGraphError_arbitrary_power d hσ T minOrder
  refine ⟨k,hmin,?_⟩
  intro A C W H B hA hC hW hH hB Q₁ Q₂ ρ₁ ρ₂ m₁ m₂ N a p hN hap hp
    hm₁ hm₂ D v τ Cap Z K hD hv hτ hCap hZ hK hratio
  have hmass := profile_graph_error_weight_bound d (p := p) hN m₁ m₂ hv hm₁ hm₂
  have hrows := dyadic_row_count_at_terminal_depth Q₁ Q₂ ρ₁ ρ₂
    (show p-a ≤ N by omega)
  have hmass' : (2:ℝ)^((d:ℝ)*(v-a)) *
      ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        |((profileModelMass m₁ N p)⁻¹*(profileModelMass m₁ N p)⁻¹)*
          ((profileModelMass m₂ N p)⁻¹*(profileModelMass m₂ N p)⁻¹)| ≤
        ((2:ℝ)^N)^(5*d) := by
    have he : (5:ℝ)*(d:ℝ) = ((5*d:ℕ):ℝ) := by simp only [Nat.cast_mul,Nat.cast_ofNat]
    rw [he,Real.rpow_natCast] at hmass
    exact hmass
  exact hk hA hC hW hH hB (one_le_pow₀ (by norm_num))
    (by positivity) hD hτ hCap hZ hK hrows hmass' hratio

end Falconer

end OAI
