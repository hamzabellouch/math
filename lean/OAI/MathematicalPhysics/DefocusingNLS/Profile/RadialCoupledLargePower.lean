import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerFixedPoint
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialScalarLargePower

namespace OAI

/-! Coupled inner profiles, uniformly for the manuscript's boundary interval and large powers. -/

open Set Filter Topology
namespace DefocusingNLS

theorem exists_radial_coupled_large_power_uniform (R : ℝ) (hR : 1 ≤ R) (hR2 : R^2 ≤ 11) :
    ∃ P : ℕ, 400 ≤ P ∧ ∀ p : ℕ, P ≤ p → ∀ c b : ℝ,
      c ∈ Icc (599/100 : ℝ) 6 → b ∈ Icc (334/1000 : ℝ) (335/1000) → ∀ lo : ℝ,
      lo ∈ Icc (1-(1/10000 : ℝ)^2/5) (1-3*(1/10000 : ℝ)^2/20) →
      ∃ H : ℝ → ℝ, Differentiable ℝ H ∧
        (∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv H) r) ∧
        H R=lo ∧ HasDerivAt H 0 0 ∧
        (∀ r ∈ Icc 0 R, H r ∈ Icc lo 1 ∧ (H r)^(p-1) ≤ (1/2 : ℝ)) ∧
        (∀ r ∈ Ioo 0 R, -deriv (deriv H) r-11/r*deriv H r+(H r)^p=
          radialAmplitudePotential c b H r*H r) := by
  obtain ⟨P₁,_,hP₁⟩ := scalar_boundary_power_small (1-3*(1/10000 : ℝ)^2/20)
    (by norm_num) (by norm_num)
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 999/1000) (by norm_num : (999/1000 : ℝ) < 1)
  have he : ∀ᶠ n : ℕ in atTop, (999/1000 : ℝ)^n < (1/5 : ℝ) :=
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/5))
  obtain ⟨N,hN⟩ := eventually_atTop.1 he
  refine ⟨max 400 (max P₁ (N+2)),le_max_left _ _,?_⟩
  intro p hp c b hc hb lo hlo
  have hp400 : 400 ≤ p := (le_max_left _ _).trans hp
  have hpP₁ : P₁ ≤ p := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hp
  have hpN : N+2 ≤ p := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hp
  have hsmall : lo^(p-1) ≤ (3/10 : ℝ) := hP₁ p hpP₁ lo (by linarith [hlo.1]) hlo.2
  have hleft : (999/1000 : ℝ)^(p-1) ≤ (1/5 : ℝ) := (hN (p-1) (by omega)).le
  have htarg : (1/5 : ℝ) ∈ Icc ((999/1000 : ℝ)^(p-1)) ((1 : ℝ)^(p-1)) :=
    ⟨hleft,by norm_num⟩
  obtain ⟨m,hm,hmp⟩ := intermediate_value_Icc (by norm_num : (999/1000 : ℝ) ≤ 1)
    (continuous_id.pow (p-1)).continuousOn htarg
  exact exists_radial_coupled_profile
    { p := p, R := R, lo := lo, c := c, b := b, m := m,
      hp := hp400, hR := hR, hR2 := hR2, hlo := hlo.1,
      hlo1 := by linarith [hlo.2], hSmall := hsmall,
      hm := hm.1, hm1 := hm.2, hmp := hmp, hc := hc, hb := hb }

theorem exists_radial_coupled_large_power (R c b : ℝ) (hR : 1 ≤ R) (hR2 : R^2 ≤ 11)
    (hc : c ∈ Icc (599/100 : ℝ) 6) (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) :
    ∃ P : ℕ, 400 ≤ P ∧ ∀ p : ℕ, P ≤ p → ∀ lo : ℝ,
      lo ∈ Icc (1-(1/10000 : ℝ)^2/5) (1-3*(1/10000 : ℝ)^2/20) →
      ∃ H : ℝ → ℝ, Differentiable ℝ H ∧
        (∀ r ∈ Ioo 0 R, DifferentiableAt ℝ (deriv H) r) ∧
        H R=lo ∧ HasDerivAt H 0 0 ∧
        (∀ r ∈ Icc 0 R, H r ∈ Icc lo 1 ∧ (H r)^(p-1) ≤ (1/2 : ℝ)) ∧
        (∀ r ∈ Ioo 0 R, -deriv (deriv H) r-11/r*deriv H r+(H r)^p=
          radialAmplitudePotential c b H r*H r) := by
  obtain ⟨P,hP,h⟩ := exists_radial_coupled_large_power_uniform R hR hR2
  exact ⟨P,hP,fun p hp lo hlo => h p hp c b hc hb lo hlo⟩

end DefocusingNLS

end OAI
