import OAI.Geometry.RCD.Heat.HeatCompactUniform
import OAI.Geometry.RCD.Heat.HeatEnergyDensity
import OAI.Geometry.RCD.Sobolev.GammaL2Stability

namespace OAI

/-! # Energy densities for compact Lipschitz functions with L² Laplacian

Heat approximation, the uniform energy estimate, and lower semicontinuity
construct the energy density in the Sobolev space itself.
-/

open Set Filter MeasureTheory
open scoped NNReal Topology ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.compact_energy_density {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (u : SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] φ)
    (d : Lp ℝ 2 (hausdorff n X)) (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d) :
    ∃ G : SobolevSpace (hausdorff n X) hX.quadratic,
      SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic u u ∧
      (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic G x| ≤ (L : ℝ) ^ 2) ∧
      energyForm (hausdorff n X) hX.quadratic G G ≤
        4 * |K| * ((L : ℝ) * Real.exp |K| * ‖u‖) ^ 2 +
          8 * ((L : ℝ) * Real.exp |K|) ^ 2 * ‖d‖ ^ 2 := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let M : ℝ≥0 := ⟨(L : ℝ) * Real.exp |K|, mul_nonneg L.coe_nonneg (Real.exp_pos _).le⟩
  let B := 4 * |K| * ((M : ℝ) * ‖u‖) ^ 2 + 8 * (M : ℝ) ^ 2 * ‖d‖ ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hLM : (L : ℝ) ≤ M := by
    change (L : ℝ) ≤ (L : ℝ) * Real.exp |K|
    nlinarith [Real.one_le_exp (abs_nonneg K), L.coe_nonneg]
  have huL := SobolevSpace.minimalSlope_le_lipschitz μ hX.quadratic u hφ hu
  have huM : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hX.quadratic u x ≤ M :=
    huL.mono fun _ hx => hx.trans hLM
  let s (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hs0 (k : ℕ) : 0 < s k := by dsimp only [s]; positivity
  have hs1 (k : ℕ) : s k ≤ 1 := by
    dsimp only [s]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  let us (k : ℕ) := heatSobolev μ hX.quadratic (s k) (hs0 k) (SobolevSpace.toLp μ hX.quadratic u)
  have hus (k : ℕ) : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hX.quadratic (us k) x ≤ M :=
    hX.heat_compact_uniform_slope hn hφ hs p _ hu.symm (hs0 k) (hs1 k)
  have hconv : Tendsto us atTop (𝓝 u) := by
    have ht := ((heatH1_continuous μ hX.quadratic u).tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [heatH1_zero, Function.comp_def, heatH1, dite_eq_left (hs0 _),
      lt_self_iff_false, dite_false, us, s] using ht
  have hex (k : ℕ) := hX.heat_compact_energy_density hn hφ hs p
    (SobolevSpace.toLp μ hX.quadratic u) hu.symm (hs0 k)
  choose Gs hGs hGsb using hex
  let hΓ := localGamma_memLp_of_bounded_gradient μ hX.quadratic u u M huM
  let H := hΓ.toLp (localGamma μ hX.quadratic u u)
  have hGs_eq (k : ℕ) : SobolevSpace.toLp μ hX.quadratic (Gs k) =
      (localGamma_memLp_of_bounded_gradient μ hX.quadratic (us k) (us k) M (hus k)).toLp
        (localGamma μ hX.quadratic (us k) (us k)) := by
    apply Lp.ext
    filter_upwards [hGs k, localGamma_self μ hX.quadratic (us k),
      (localGamma_memLp_of_bounded_gradient μ hX.quadratic (us k) (us k) M (hus k)).coeFn_toLp]
      with x hx hy hz
    exact hx.trans (hy.symm.trans hz.symm)
  have hGconv : Tendsto (fun k => SobolevSpace.toLp μ hX.quadratic (Gs k)) atTop (𝓝 H) := by
    exact (gammaL2_tendsto μ hX.quadratic M hus huM hconv).congr'
      (Eventually.of_forall fun k => (hGs_eq k).symm)
  have hE (k : ℕ) : energyForm μ hX.quadratic (Gs k) (Gs k) ≤ B :=
    hX.heat_compact_uniform_gamma_energy hn hφ hs p u hu d hd (hs0 k) (hs1 k) (Gs k) (hGs k)
  have henergy : energyLp μ H ≤ ENNReal.ofReal (B / 2) := by
    apply (energyLp_le_liminf μ hGconv).trans
    apply liminf_le_of_frequently_le'
    apply Eventually.frequently
    apply Eventually.of_forall
    intro k
    have hh := hE k
    rw [energyForm_self] at hh
    have he : energyLp μ (SobolevSpace.toLp μ hX.quadratic (Gs k)) =
        ENNReal.ofReal (SobolevSpace.energy μ hX.quadratic (Gs k)) :=
      (ENNReal.ofReal_toReal (Gs k).property).symm
    rw [he]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  let G : SobolevSpace μ hX.quadratic :=
    ⟨H, ne_top_of_le_ne_top ENNReal.ofReal_ne_top henergy⟩
  refine ⟨G, hΓ.coeFn_toLp, ?_, ?_⟩
  · filter_upwards [hΓ.coeFn_toLp, localGamma_self μ hX.quadratic u, huL,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic u)]
      with x hx hy hL h0
    change |H x| ≤ (L : ℝ) ^ 2
    rw [hx, hy, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ h0 hL 2
  · have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top henergy
    rw [ENNReal.toReal_ofReal (by positivity)] at he
    change SobolevSpace.energy μ hX.quadratic G ≤ B / 2 at he
    rw [energyForm_self]
    change 2 * SobolevSpace.energy μ hX.quadratic G ≤ B
    linarith

end RegularPointCoordinates

end

end OAI
