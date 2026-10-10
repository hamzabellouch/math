import OAI.MeasureTheory.Falconer.Graphs.TwoProfileGraph
import OAI.MeasureTheory.Falconer.Graphs.ProfileGraphError

namespace OAI

/-! # Common graph scale and uniform error for the two outer profiles -/

namespace Falconer
open Set MeasureTheory

namespace JetStateGraphData
variable {n k : ℕ} {α B : ℝ}

def withGraphScale (G : JetStateGraphData n k α B) (D : ℝ) (hD : G.Dgraph ≤ D) :
    JetStateGraphData n k α B :=
  { G with
    Dgraph := D
    Dgraph_one := G.Dgraph_one.trans hD
    symbol_scale := G.symbol_scale.trans hD
    cap_scale := G.cap_scale.trans hD
    endpoint_scale := G.endpoint_scale.trans
      (mul_le_mul_of_nonneg_left hD (div_nonneg G.τ_pos.le (by norm_num))) }

end JetStateGraphData

theorem exists_two_graph_error_order (m : ℕ) {σ : ℝ} (hσ : 0 < σ)
    (T : ℝ) (minOrder : ℕ := 0) :
    ∃ k : ℕ, minOrder ≤ k ∧ ∀ {α B A C W Cap V : ℝ},
      0 ≤ A → 0 ≤ C → 0 ≤ W → 0 ≤ Cap → 0 ≤ V →
      ∀ G H : JetStateGraphData (m+1) k α B, JetGraphAlignment G H →
      G.v ≤ G.N →
      (G.caps.card:ℝ) ≤ Cap*((2:ℝ)^G.N)^(m+3) →
      16*G.Dgraph/((2:ℝ)^G.v*G.τ) ≤ V*((2:ℝ)^G.N)^(-(26*σ)) →
      G.twoProfileError H A C W (T+(11*(m+3):ℕ)) ≤
        Cap^2*((A*(4^k*G.capBound)*(sphereMeasure (m+3)).real univ*(4*W))*V^k+
          C*((sphereMeasure (m+3)).real univ)^2)*((2:ℝ)^G.N)^(-T) := by
  obtain ⟨k,hmin,hk⟩ := profile_graph_error_arbitrary_power (m+3) hσ T minOrder
  refine ⟨k,hmin,?_⟩
  intro α B A C W Cap V hA hC hW hCap hV G H hsame hv hcard hratio
  have hG : G.profile ((G.a:ℝ)/G.N) ≤ (m+3:ℕ) :=
    (G.regular.range _ ⟨by positivity,by
      apply (div_le_one (Nat.cast_pos.mpr G.N_pos)).mpr
      exact_mod_cast G.ap.trans G.pN⟩).2
  have hH : H.profile ((G.a:ℝ)/G.N) ≤ (m+3:ℕ) := by
    have hh := (H.regular.range ((H.a:ℝ)/H.N) ⟨by positivity,by
      apply (div_le_one (Nat.cast_pos.mpr H.N_pos)).mpr
      exact_mod_cast H.ap.trans H.pN⟩).2
    simpa only [hsame.a,hsame.N] using hh
  have hh := hk hA hC hW G.capBound_nonneg (by norm_num : (0:ℝ) ≤ 1)
    (G.Q.descendant G.X) (H.Q.descendant H.X) G.ρ H.ρ G.profile H.profile
    G.N G.a G.p G.N_pos G.ap G.pN hG hH
    (zero_le_one.trans G.Dgraph_one) hv G.τ_pos hCap hV hcard hratio
  simpa only [JetStateGraphData.twoProfileError,hsame.N,hsame.a,hsame.p,
    mul_one,one_mul,mul_assoc] using hh

end Falconer

end OAI
