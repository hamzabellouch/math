import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def SuperpolynomialGrowth : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n≥N, ∀ v : V, n^M≤(G.vertexBall v n).ncard

lemma exists_volume_radius (hg : G.SuperpolynomialGrowth) (s : ℕ) :
    ∃ r : ℕ, 1≤r ∧ ∀ v : V, s^4≤(G.vertexBall v r).ncard := by
  obtain ⟨N,hN⟩ := hg 1
  refine ⟨N+s^4+1,by omega,?_⟩
  intro v
  have hh := hN (N+s^4+1) (by omega) v
  simpa only [pow_one] using (show s^4≤N+s^4+1 by omega).trans (by simpa only [pow_one] using hh)

lemma superpolynomial_radius_log (hg : G.SuperpolynomialGrowth)
    (M : ℕ) (hM : 1≤M) :
    ∃ C : ℝ, 0≤C ∧ ∀ s : ℕ, 1 ≤ s →
      ∃ r : ℕ, 1≤r ∧ (∀ v : V, s^4≤(G.vertexBall v r).ncard) ∧
        Real.log r ≤ 4/(M:ℝ)*Real.log s+C := by
  obtain ⟨N,hN⟩ := hg M
  let C := Real.log ((N:ℝ)+2)+Real.log 2
  have hlog2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hC : 0≤C := add_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)) hlog2
  refine ⟨C,hC,?_⟩
  intro s hs
  let H := G.exists_volume_radius hg s
  let r := Nat.find H
  obtain ⟨hr,hrV⟩ := Nat.find_spec H
  change 1≤r at hr
  change ∀ v, s^4≤(G.vertexBall v r).ncard at hrV
  refine ⟨r,hr,hrV,?_⟩
  have hrpos : (0:ℝ)<r := Nat.cast_pos.mpr (by omega)
  have hspos : (0:ℝ)<s := Nat.cast_pos.mpr (by omega)
  have hlogs : 0≤Real.log s := Real.log_nonneg (by exact_mod_cast hs)
  have hMp : (0:ℝ)<M := Nat.cast_pos.mpr (by omega)
  by_cases hsmall : r≤N+2
  · have hh := Real.log_le_log hrpos (Nat.cast_le.mpr hsmall)
    simp only [Nat.cast_add,Nat.cast_ofNat] at hh
    dsimp [C]
    have hn : 0≤4/(M:ℝ)*Real.log s := mul_nonneg (by positivity) hlogs
    linarith
  · have hr2 : 2≤r := by omega
    have hprev : ¬(1≤r-1 ∧ ∀ v : V, s^4≤(G.vertexBall v (r-1)).ncard) :=
      Nat.find_min H (by omega)
    have hex : ∃ v : V, (G.vertexBall v (r-1)).ncard<s^4 := by
      by_contra! hn
      exact hprev ⟨by omega, hn⟩
    obtain ⟨v,hv⟩ := hex
    have hpow : (r-1)^M<s^4 := (hN (r-1) (by omega) v).trans_lt hv
    have hpredpos : (0:ℝ)<(r-1:ℕ) := Nat.cast_pos.mpr (by omega)
    have hpowreal : ((r-1:ℕ):ℝ)^M<(s:ℝ)^4 := by exact_mod_cast hpow
    have hl := Real.log_lt_log (pow_pos hpredpos _) hpowreal
    rw [Real.log_pow,Real.log_pow] at hl
    have hless : Real.log (r-1:ℕ) ≤ 4/(M:ℝ)*Real.log s := by
      apply (mul_le_mul_iff_right₀ hMp).mp
      calc
        _ ≤ 4*Real.log s := hl.le
        _ = _ := by field_simp
    have hrle : (r:ℝ)≤2*((r-1:ℕ):ℝ) := by exact_mod_cast (show r≤2*(r-1) by omega)
    have hlogr := Real.log_le_log hrpos hrle
    rw [Real.log_mul (by norm_num) hpredpos.ne'] at hlogr
    dsimp [C]
    have hn := Real.log_nonneg (show 1≤(N:ℝ)+2 by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
