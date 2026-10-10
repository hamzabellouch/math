import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.GrowthAlternatives
import OAI.Probability.CriticalPercolation.Criticality.SubexponentialVolumes
import OAI.Probability.CriticalPercolation.Modular.GraphModular

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stabilizerOrbit_subset_ball {x y : V} {n : ℕ} (hy : y ∈ G.vertexBall x n) :
    G.stabilizerOrbit x y ⊆ G.vertexBall x n := by
  intro z hz
  obtain ⟨φ,hx,rfl⟩ := G.mem_stabilizerOrbit.mp hz
  rw [←hx]
  exact (Aut.vertexBall_mem G φ x y n).mpr hy

lemma Aut.pow_vertex_ball (φ : G.Aut) (x : V) (C : ℕ)
    (hx : φ.vertex x ∈ G.vertexBall x C) (n : ℕ) :
    (φ^n).vertex x ∈ G.vertexBall x (n*C) := by
  induction n with
  | zero =>
    rw [pow_zero,Nat.zero_mul]
    exact G.mem_vertexBall_self x 0
  | succ n ih =>
    have hstep := (Aut.vertexBall_mem G (φ^n) x (φ.vertex x) C).mpr hx
    have hh := G.vertexBall_add ih C hstep
    have heq : (φ^(n+1)).vertex x = (φ^n).vertex (φ.vertex x) := by rw [pow_succ]; rfl
    simpa only [Nat.add_mul,Nat.one_mul,←heq] using hh

lemma Aut.modularRatio_pow (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (φ : G.Aut) (x : V) (n : ℕ) :
    G.modularRatio x ((φ^n).vertex x) = (G.modularRatio x (φ.vertex x))^n := by
  induction n with
  | zero =>
    rw [pow_zero,pow_zero]
    exact G.modularRatio_self x
  | succ n ih =>
    have heq : (φ^(n+1)).vertex x = (φ^n).vertex (φ.vertex x) := by rw [pow_succ]; rfl
    rw [heq,← G.modularRatio_cocycle hc hl x ((φ^n).vertex x),Aut.modularRatio,ih,pow_succ]

lemma modularRatio_le_suborbitCard (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : G.modularRatio x y ≤ (G.suborbitCard x y : ℝ) := by
  apply div_le_self (Nat.cast_nonneg _)
  exact_mod_cast G.suborbitCard_pos hc hl y x

lemma modular_power_log_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (φ : G.Aut) (x : V) (C : ℕ) (hx : φ.vertex x ∈ G.vertexBall x C) (n : ℕ) :
    (n:ℝ)*Real.log (G.modularRatio x (φ.vertex x)) ≤
      Real.log ((G.vertexBall x (n*C)).ncard : ℝ) := by
  have hp := G.modularRatio_pos hc hl x (φ.vertex x)
  have hh : (G.modularRatio x (φ.vertex x))^n ≤ (G.vertexBall x (n*C)).ncard := by
    rw [←Aut.modularRatio_pow G hc hl φ x n]
    apply (G.modularRatio_le_suborbitCard hc hl x _).trans
    exact_mod_cast Set.ncard_le_ncard
      (G.stabilizerOrbit_subset_ball (Aut.pow_vertex_ball G φ x C hx n))
      (G.vertexBall_finite hl x (n*C))
  have hlog := Real.log_le_log (pow_pos hp n) hh
  rwa [Real.log_pow] at hlog

lemma subexponential_modularRatio_le_one (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hg : G.SubexponentialGrowth) (φ : G.Aut) (x : V) :
    G.modularRatio x (φ.vertex x) ≤ 1 := by
  by_contra hn
  have hr : 1 < G.modularRatio x (φ.vertex x) := lt_of_not_ge hn
  have hlog : 0 < Real.log (G.modularRatio x (φ.vertex x)) := Real.log_pos hr
  obtain ⟨C₀,hC₀⟩ := G.finite_subset_vertexBall hc x (Set.finite_singleton (φ.vertex x))
  let C := C₀+1
  have hC : 0 < C := by omega
  have hx : φ.vertex x ∈ G.vertexBall x C :=
    G.vertexBall_mono x (Nat.le_succ _) (hC₀ (Set.mem_singleton _))
  let a := Real.log (G.modularRatio x (φ.vertex x))
  have hCr : (0:ℝ)<C := Nat.cast_pos.mpr hC
  obtain ⟨N,hN⟩ := hg x (a/(2*C)) (div_pos hlog (by positivity))
  let n := N+1
  have hn : 0<n := by omega
  have hnC : N ≤ n*C := (Nat.le_succ N).trans (Nat.le_mul_of_pos_right n hC)
  have hlo := G.modular_power_log_bound hc hl φ x C hx n
  have hhi := hN (n*C) hnC
  have heq : (a/(2*(C:ℝ))) * ((n*C:ℕ):ℝ) = (n:ℝ)*a/2 := by
    push_cast
    field_simp
  change (n:ℝ)*a ≤ _ at hlo
  rw [heq] at hhi
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  nlinarith [mul_pos hnr hlog]

lemma subexponential_combinatoriallyUnimodular (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hg : G.SubexponentialGrowth) : G.CombinatoriallyUnimodular := by
  intro φ x
  have h1 := G.subexponential_modularRatio_le_one hc hl hg φ x
  have h2 := G.subexponential_modularRatio_le_one hc hl hg φ⁻¹ (φ.vertex x)
  have heq : (φ⁻¹).vertex (φ.vertex x) = x := φ.vertex.symm_apply_apply x
  rw [heq] at h2
  unfold modularRatio at h1 h2
  have hp1 : (0:ℝ)<G.suborbitCard x (φ.vertex x) := Nat.cast_pos.mpr (G.suborbitCard_pos hc hl x (φ.vertex x))
  have hp2 : (0:ℝ)<G.suborbitCard (φ.vertex x) x := Nat.cast_pos.mpr (G.suborbitCard_pos hc hl (φ.vertex x) x)
  have ha := (div_le_one hp2).mp h1
  have hb := (div_le_one hp1).mp h2
  exact_mod_cast le_antisymm ha hb

lemma exponential_of_not_combinatoriallyUnimodular [Nonempty V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hu : ¬ G.CombinatoriallyUnimodular) :
    ∃ a : ℝ, 0<a ∧ ∃ N : ℕ, ∀ n≥N, ∀ v : V,
      a*n ≤ Real.log ((G.vertexBall v n).ncard : ℝ) := by
  rcases G.growth_alternative hc hl hq with hg | hg
  · exact False.elim (hu (G.subexponential_combinatoriallyUnimodular hc hl hg))
  · exact hg

end CriticalPercolation.BondGraph
end
end

end OAI
