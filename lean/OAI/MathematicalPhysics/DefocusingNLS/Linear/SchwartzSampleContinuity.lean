import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSamplingLocalBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPeriodizationLimit
import Mathlib.Analysis.Normed.Group.Tannery

namespace OAI

/-! # Continuity of a fixed Schwartz sample in the torus radius -/

open Filter Topology
open scoped SchwartzMap ENNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem continuous_schwartzTorusSample_coordinate (a k : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (K : 𝓢(E, ℂ)) (n : frequencyLattice) :
    Continuous (fun L : Radius => schwartzTorusSample a k L.1 ha1 hk L.2 K n) := by
  have hpos (L : Radius) : L.1 ≠ 0 := (lt_of_lt_of_le zero_lt_one L.2).ne'
  have hlo : Continuous (fun L : Radius => L.1 ^ (2 * a)) :=
    continuous_subtype_val.rpow_const (fun L => Or.inl (hpos L))
  have hhi : Continuous (fun L : Radius => L.1 ^ (12 - 2 * k)) :=
    continuous_subtype_val.rpow_const (fun L => Or.inl (hpos L))
  have hw : Continuous (fun L : Radius => expandingSobolevWeight a k L.1 n) := by
    unfold expandingSobolevWeight expandingSobolevWeightSq
    exact continuous_const.mul (Real.continuous_sqrt.comp
      ((hlo.mul continuous_const).add (hhi.mul continuous_const)))
  have hv : Continuous (fun L : Radius => ((2 * Real.pi * L.1) ^ (12 : ℕ))⁻¹) :=
    ((continuous_const.mul continuous_subtype_val).pow 12).inv₀ (fun L => by
      exact pow_ne_zero _ (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (hpos L)))
  have hx : Continuous (fun L : Radius => L.1⁻¹ • (n : E)) :=
    (continuous_subtype_val.inv₀ hpos).smul continuous_const
  change Continuous (fun L : Radius => (expandingSobolevWeight a k L.1 n : ℂ) *
    ((((2 * Real.pi * L.1) ^ (12 : ℕ))⁻¹ : ℝ) * K (L.1⁻¹ • (n : E))))
  exact (Complex.continuous_ofReal.comp hw).mul
    ((Complex.continuous_ofReal.comp hv).mul (K.continuous.comp hx))

theorem continuous_schwartzTorusSample (a k : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (K : 𝓢(E, ℂ)) :
    Continuous (fun L : Radius => schwartzTorusSample a k L.1 ha1 hk L.2 K) := by
  rw [continuous_iff_continuousAt]
  intro L₀
  obtain ⟨D, hD, hbD⟩ := schwartzTorusSample_local_bound a k (L₀.1 + 1) ha1 hk
    (by linarith [L₀.2]) K
  have hnear : ∀ᶠ L : Radius in 𝓝 L₀, L.1 ≤ L₀.1 + 1 :=
    (continuous_subtype_val.continuousAt.tendsto.eventually
      (eventually_lt_nhds (by linarith : L₀.1 < L₀.1 + 1))).mono
        (fun _ h => h.le)
  have hs : Summable (fun n : frequencyLattice => ((1 + ‖n‖ ^ 2) ^ (12 : ℕ))⁻¹) := by
    convert summable_sobolev_variances 0 12 (by norm_num) using 1
    ext n
    norm_num [Real.rpow_neg]
  have hb : ∀ᶠ L : Radius in 𝓝 L₀, ∀ n : frequencyLattice,
      ‖schwartzTorusSample a k L.1 ha1 hk L.2 K n -
        schwartzTorusSample a k L₀.1 ha1 hk L₀.2 K n‖ ^ 2 ≤
          4 * D * ((1 + ‖n‖ ^ 2) ^ (12 : ℕ))⁻¹ := by
    filter_upwards [hnear] with L hL n
    have h₁ := hbD L.1 L.2 hL n
    have h₀ := hbD L₀.1 L₀.2 (by linarith) n
    have ht := norm_sub_le (schwartzTorusSample a k L.1 ha1 hk L.2 K n)
      (schwartzTorusSample a k L₀.1 ha1 hk L₀.2 K n)
    have hsq := sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2 ht
    nlinarith [sq_nonneg (‖schwartzTorusSample a k L.1 ha1 hk L.2 K n‖ -
      ‖schwartzTorusSample a k L₀.1 ha1 hk L₀.2 K n‖)]
  have hlim := tendsto_tsum_of_dominated_convergence (hs.mul_left (4 * D))
    (f := fun L n => ‖schwartzTorusSample a k L.1 ha1 hk L.2 K n -
      schwartzTorusSample a k L₀.1 ha1 hk L₀.2 K n‖ ^ 2)
    (g := fun _ => (0 : ℝ)) (𝓕 := 𝓝 L₀)
    (by
      intro n
      have hc : Continuous (fun L : Radius =>
          ‖schwartzTorusSample a k L.1 ha1 hk L.2 K n -
            schwartzTorusSample a k L₀.1 ha1 hk L₀.2 K n‖ ^ 2) :=
        (((continuous_schwartzTorusSample_coordinate a k ha1 hk K n).sub
          continuous_const).norm.fun_pow 2)
      simpa using (hc.continuousAt (x := L₀)).tendsto)
    (by
      filter_upwards [hb] with L hL n
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hL n)
  have hsq : Tendsto (fun L : Radius => ‖schwartzTorusSample a k L.1 ha1 hk L.2 K -
      schwartzTorusSample a k L₀.1 ha1 hk L₀.2 K‖ ^ 2) (𝓝 L₀) (𝓝 0) := by
    have heq (L : Radius) := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
      (schwartzTorusSample a k L.1 ha1 hk L.2 K - schwartzTorusSample a k L₀.1 ha1 hk L₀.2 K)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, lp.coeFn_sub, Pi.sub_apply] at heq
    simpa only [heq, tsum_zero] using hlim
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

end DefocusingNLS

end OAI
