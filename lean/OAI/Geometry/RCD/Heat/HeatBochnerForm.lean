import OAI.Geometry.RCD.Heat.HeatEnergyDensity
import OAI.Geometry.RCD.Sobolev.GammaL2Bound

namespace OAI

/-! # Weak Bochner with ordinary bounded Sobolev tests

The energy density is already Sobolev. Strong heat convergence in that
space and L² convergence of the mixed pairing remove the smoothed weight.
-/

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_bochner_sobolev_test {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) {t : ℝ} (ht : 0 < t)
    (G : SobolevSpace (hausdorff n X) hX.quadratic) (L : ℝ≥0)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      fun x => (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht f) x) ^ 2)
    (hF : ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic t ht f) x ≤ L)
    (w : SobolevSpace (hausdorff n X) hX.quadratic) (C : ℝ≥0)
    (hw0 : 0 ≤ SobolevSpace.toLp (hausdorff n X) hX.quadratic w)
    (hw : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic w x| ≤ C) :
    let F := heatSobolev (hausdorff n X) hX.quadratic t ht f
    let D := heatSobolevMap (hausdorff n X) hX.quadratic (t / 2) (half_pos ht)
      (-heatGeneratorAt (hausdorff n X) hX.quadratic (t - t / 2) f)
    energyForm (hausdorff n X) hX.quadratic G w +
      2 * K * inner ℝ (SobolevSpace.toLp (hausdorff n X) hX.quadratic w)
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic G) +
      2 * weightedGamma (hausdorff n X) hX.quadratic
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic w) F D ≤ 0 := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let F := heatSobolev μ hX.quadratic t ht f
  let D := heatSobolevMap μ hX.quadratic (t / 2) (half_pos ht)
    (-heatGeneratorAt μ hX.quadratic (t - t / 2) f)
  let W := SobolevSpace.toLp μ hX.quadratic w
  let H := SobolevSpace.toLp μ hX.quadratic G
  have hΓ := localGamma_memLp_of_bounded_gradient μ hX.quadratic F D L hF
  let E (s : ℝ) := energyForm μ hX.quadratic (heatH1 μ hX.quadratic s w) G +
    2 * K * inner ℝ (heatAt μ hX.quadratic s W) H +
    2 * weightedGamma μ hX.quadratic (heatAt μ hX.quadratic s W) F D
  have hlimit : Tendsto E (𝓝[>] 0) (𝓝 (E 0)) := by
    have h₁ : Tendsto (fun s => energyForm μ hX.quadratic (heatH1 μ hX.quadratic s w) G)
        (𝓝 0) (𝓝 (energyForm μ hX.quadratic w G)) := by
      have hh := ((energyForm_continuous μ hX.quadratic).comp
        ((heatH1_continuous μ hX.quadratic w).prodMk (continuous_const (y := G)))).tendsto 0
      simpa only [Function.comp_def, heatH1, lt_self_iff_false, dite_false] using hh
    have h₂ : Tendsto (fun s => inner ℝ (heatAt μ hX.quadratic s W) H)
        (𝓝 0) (𝓝 (inner ℝ W H)) := by
      have hh : Tendsto (fun s => inner ℝ (heatAt μ hX.quadratic s W) H) (𝓝 0)
          (𝓝 (inner ℝ (heatAt μ hX.quadratic 0 W) H)) :=
        ((heatAt_continuous μ hX.quadratic W).tendsto 0).inner tendsto_const_nhds
      simpa only [heatAt_zero, one_apply_eq_self] using hh
    have h₃ := weightedGamma_heat_tendsto μ hX.quadratic F D hΓ W
    have hh := (h₁.add (h₂.const_mul (2 * K))).add (h₃.const_mul 2)
    have hh' : Tendsto E (𝓝 (0 : ℝ)) (𝓝 (E 0)) := by
      simpa only [E, heatH1, lt_self_iff_false, dite_false, heatAt_zero, one_apply_eq_self] using hh
    exact hh'.mono_left nhdsWithin_le_nhds
  have hE (s : ℝ) (hs : 0 < s) : E s ≤ 0 := by
    have hb := hX.heat_weak_bochner K n hn p f W hw0 C hw t s ht hs H hG.symm
    have hI : (∫ x, heatAt μ hX.quadratic s W x *
        (SobolevSpace.minimalSlope μ hX.quadratic F x) ^ 2 ∂μ) =
        inner ℝ (heatAt μ hX.quadratic s W) H := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hG] with x hx
      change H x = (SobolevSpace.minimalSlope μ hX.quadratic F x) ^ 2 at hx
      simp only [Real.inner_apply, hx]
    have hJ : (∫ x, (-heatGeneratorAt μ hX.quadratic s W) x * H x ∂μ) =
        -energyForm μ hX.quadratic (heatH1 μ hX.quadratic s w) G := by
      have hi : (∫ x, (-heatGeneratorAt μ hX.quadratic s W) x * H x ∂μ) =
          inner ℝ (-heatGeneratorAt μ hX.quadratic s W) H := by
        simp only [L2.inner_def, Real.inner_apply]
      rw [hi, heatGeneratorAt_of_pos μ hX.quadratic s hs, inner_neg_left,
        ← heatGenerator_form]
      simp only [heatH1, dite_eq_left hs, W]
    change K * _ + weightedGamma μ hX.quadratic (heatAt μ hX.quadratic s W) F D ≤
      (1 / 2 : ℝ) * _ at hb
    rw [hI, hJ] at hb
    dsimp only [E]
    linarith
  have h0 : E 0 ≤ 0 := le_of_tendsto hlimit (eventually_nhdsWithin_of_forall hE)
  change energyForm μ hX.quadratic G w + 2 * K * inner ℝ W H +
    2 * weightedGamma μ hX.quadratic W F D ≤ 0
  simpa only [E, heatH1, lt_self_iff_false, dite_false, heatAt_zero, one_apply_eq_self,
    energyForm_comm μ hX.quadratic w G] using h0

end RegularPointCoordinates

end

end OAI
