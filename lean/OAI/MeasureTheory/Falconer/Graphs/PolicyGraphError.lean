import OAI.MeasureTheory.Falconer.Graphs.PolicyGraphData
import OAI.MeasureTheory.Falconer.Graphs.ProfileGraphError

namespace OAI

/-! # Cap counts and error orders for the actual policy graph step -/

namespace Falconer
open Set MeasureTheory

theorem policyGraphRadius_inv_bound {N a p : ℕ} {σ c₀ : ℝ}
    (hp : p ≤ N) (hσ : 0 ≤ σ) (hc₀ : 0 < c₀) :
    (policyGraphRadius N a p σ c₀)⁻¹ ≤ (c₀⁻¹+1)*(2:ℝ)^N := by
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hexp : -(N:ℝ) ≤ (a:ℝ)-p+10*σ*N := by
    have hp' : (p:ℝ) ≤ N := by exact_mod_cast hp
    have ha : (0:ℝ) ≤ a := Nat.cast_nonneg a
    have hh : 0 ≤ 10*σ*(N:ℝ) := by positivity
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hexp
  have hinv : ((2:ℝ)^((a:ℝ)-p+10*σ*N))⁻¹ ≤ (2:ℝ)^N := by
    have hh := (inv_le_inv₀ (by positivity : 0 < (2:ℝ)^((a:ℝ)-p+10*σ*N))
      (by positivity : 0 < (2:ℝ)^(-(N:ℝ)))).mpr hpow
    simpa only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),inv_inv,
      Real.rpow_natCast] using hh
  have hc : c₀⁻¹ ≤ (c₀⁻¹+1)*(2:ℝ)^N := by
    have hh := mul_le_mul_of_nonneg_left hR (show 0 ≤ c₀⁻¹+1 by positivity)
    nlinarith [inv_pos.mpr hc₀]
  have hr : (2:ℝ)^N ≤ (c₀⁻¹+1)*(2:ℝ)^N := by
    nlinarith [inv_pos.mpr hc₀,pow_pos (by norm_num : (0:ℝ) < 2) N]
  unfold policyGraphRadius
  by_cases h : c₀ ≤ (2:ℝ)^((a:ℝ)-p+10*σ*N)
  · simpa only [min_eq_left h] using hc
  · simpa only [min_eq_right (le_of_not_ge h)] using hinv.trans hr

theorem policyGraphCap_count {d N a p : ℕ} {σ c₀ : ℝ}
    (hp : p ≤ N) (hσ : 0 ≤ σ) (hc₀ : 0 < c₀) {K : ℕ}
    (hK : (K:ℝ) ≤ (4/policyGraphRadius N a p σ c₀+1)^d) :
    (K:ℝ) ≤ (4*c₀⁻¹+5)^d*((2:ℝ)^N)^d := by
  have hi := policyGraphRadius_inv_bound (a := a) hp hσ hc₀
  have hR : 1 ≤ (2:ℝ)^N := one_le_pow₀ (by norm_num)
  have hδ : 0 < policyGraphRadius N a p σ c₀ :=
    lt_min hc₀ (by positivity)
  calc
    _ ≤ (4/policyGraphRadius N a p σ c₀+1)^d := hK
    _ ≤ ((4*c₀⁻¹+5)*(2:ℝ)^N)^d := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_eq_mul_inv]
      nlinarith
    _ = _ := mul_pow _ _ _

theorem exists_policy_graph_error_order (m : ℕ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ) (minOrder : ℕ := 0) :
    ∃ k : ℕ, minOrder ≤ k ∧ ∀ {α B H C W Cap V : ℝ},
      0 ≤ H → 0 ≤ C → 0 ≤ W → 0 ≤ Cap → 0 ≤ V →
      ∀ G : JetStateGraphData (m+1) k α B,
      G.v ≤ G.N →
      (G.caps.card:ℝ) ≤ Cap*((2:ℝ)^G.N)^(m+3) →
      16*G.Dgraph/((2:ℝ)^G.v*G.τ) ≤ V*((2:ℝ)^G.N)^(-(26*σ)) →
      G.error H C W (T+(11*(m+3):ℕ)) ≤
        Cap^2*((H*(4^k*G.capBound)*(sphereMeasure (m+3)).real univ*(4*W))*V^k+
          C*((sphereMeasure (m+3)).real univ)^2)*((2:ℝ)^G.N)^(-T) := by
  obtain ⟨k,hmin,hk⟩ := profile_graph_error_arbitrary_power (m+3) hσ T minOrder
  refine ⟨k,hmin,?_⟩
  intro α B H C W Cap V hH hC hW hCap hV G hv hcard hratio
  have hm : G.profile ((G.a:ℝ)/G.N) ≤ (m+3:ℕ) :=
    (G.regular.range _ ⟨by positivity,by
      apply (div_le_one (Nat.cast_pos.mpr G.N_pos)).mpr
      exact_mod_cast G.ap.trans G.pN⟩).2
  have hh := hk hH hC hW G.capBound_nonneg (by norm_num : (0:ℝ) ≤ 1)
    (G.Q.descendant G.X) (G.Q.descendant G.Y) G.ρ G.ρ G.profile G.profile
    G.N G.a G.p G.N_pos G.ap G.pN hm hm
    (zero_le_one.trans G.Dgraph_one) hv G.τ_pos hCap hV hcard hratio
  simpa only [JetStateGraphData.error,mul_one,one_mul,mul_assoc] using hh

end Falconer

end OAI
