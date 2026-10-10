import OAI.Geometry.RCD.Sobolev.CompactEnergyDensity
import OAI.Geometry.RCD.Sobolev.BochnerSobolevLimit

namespace OAI

/-! # Bochner positivity for compact Lipschitz functions with L² Laplacian

The mixed derivative is integrated by parts before taking the heat-time
limit. Only the L² Laplacian occurs in the resulting formula.
-/

open Set Filter MeasureTheory
open scoped NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.compact_bochner_sobolev_test {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (u : SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] φ)
    (d : Lp ℝ 2 (hausdorff n X)) (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (G : SobolevSpace (hausdorff n X) hX.quadratic)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic u u)
    (w : SobolevSpace (hausdorff n X) hX.quadratic) {v : X → ℝ}
    (hv : Measurable v) (hw : SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[hausdorff n X] v)
    (C : ℝ≥0) (hvb : ∀ x, |v x| ≤ C) (hv0 : ∀ x, 0 ≤ v x) :
    0 ≤ -(1 / 2 : ℝ) * energyForm (hausdorff n X) hX.quadratic G w -
      K * inner ℝ (SobolevSpace.toLp (hausdorff n X) hX.quadratic w)
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic G) +
      (∫ x, v x * (d x) ^ 2 ∂hausdorff n X) +
      weightedGamma (hausdorff n X) hX.quadratic d u w := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let M : ℝ≥0 := ⟨(L : ℝ) * Real.exp |K|, mul_nonneg L.coe_nonneg (Real.exp_pos _).le⟩
  let B := 4 * |K| * ((M : ℝ) * ‖u‖) ^ 2 + 8 * (M : ℝ) ^ 2 * ‖d‖ ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hLM : (L : ℝ) ≤ M := by
    change (L : ℝ) ≤ (L : ℝ) * Real.exp |K|
    nlinarith [Real.one_le_exp (abs_nonneg K), L.coe_nonneg]
  have huM : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hX.quadratic u x ≤ M :=
    (SobolevSpace.minimalSlope_le_lipschitz μ hX.quadratic u hφ hu).mono fun _ hx => hx.trans hLM
  have hwC : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hX.quadratic w x| ≤ C :=
    hw.mono fun x hx => hx ▸ hvb x
  have hw0 : 0 ≤ SobolevSpace.toLp μ hX.quadratic w := by
    apply (Lp.coeFn_nonneg _).mp
    exact hw.mono fun x hx => hx ▸ hv0 x
  let s (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hs0 (k : ℕ) : 0 < s k := by dsimp only [s]; positivity
  have hs1 (k : ℕ) : s k ≤ 1 := by
    dsimp only [s]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  let us (k : ℕ) := heatSobolev μ hX.quadratic (s k) (hs0 k) (SobolevSpace.toLp μ hX.quadratic u)
  let ds (k : ℕ) := heatAt μ hX.quadratic (s k) d
  let Ds (k : ℕ) := heatSobolevMap μ hX.quadratic (s k / 2) (half_pos (hs0 k))
    (-heatGeneratorAt μ hX.quadratic (s k - s k / 2) (SobolevSpace.toLp μ hX.quadratic u))
  have hDs (k : ℕ) : SobolevSpace.toLp μ hX.quadratic (Ds k) = ds k :=
    heatTail_laplacian_toLp μ hX.quadratic u d hd (hs0 k)
  have hus (k : ℕ) : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hX.quadratic (us k) x ≤ M :=
    hX.heat_compact_uniform_slope hn hφ hs p _ hu.symm (hs0 k) (hs1 k)
  have hconv : Tendsto us atTop (𝓝 u) := by
    have ht := ((heatH1_continuous μ hX.quadratic u).tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [heatH1_zero, Function.comp_def, heatH1, dite_eq_left (hs0 _),
      lt_self_iff_false, dite_false, us, s] using ht
  have hdconv : Tendsto ds atTop (𝓝 d) := by
    have ht := ((heatAt_continuous μ hX.quadratic d).tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [heatAt_zero, one_apply_eq_self, Function.comp_def, ds, s] using ht
  have hex (k : ℕ) := hX.heat_compact_energy_density hn hφ hs p
    (SobolevSpace.toLp μ hX.quadratic u) hu.symm (hs0 k)
  choose Gs hGs hGsb using hex
  have hGsΓ (k : ℕ) : SobolevSpace.toLp μ hX.quadratic (Gs k) =ᵐ[μ]
      localGamma μ hX.quadratic (us k) (us k) :=
    (hGs k).trans (localGamma_self μ hX.quadratic (us k)).symm
  have hE (k : ℕ) : energyForm μ hX.quadratic (Gs k) (Gs k) ≤ B :=
    hX.heat_compact_uniform_gamma_energy hn hφ hs p u hu d hd (hs0 k) (hs1 k) (Gs k) (hGs k)
  have hb (k : ℕ) : energyForm μ hX.quadratic (Gs k) w +
      2 * K * inner ℝ (SobolevSpace.toLp μ hX.quadratic w) (SobolevSpace.toLp μ hX.quadratic (Gs k)) -
      2 * (∫ x, v x * (ds k x) ^ 2 ∂μ) - 2 * weightedGamma μ hX.quadratic (ds k) (us k) w ≤ 0 := by
    have hboch := hX.heat_bochner_sobolev_test hn p _ (hs0 k) (Gs k) M (hGs k) (hus k) w C hw0 hwC
    have hmix := weakLaplacian_mixed_identity_L2 μ hX.quadratic (us k) (Ds k) w C M hwC (hus k)
      (heatTail_weak_laplacian μ hX.quadratic (s k) (hs0 k) (SobolevSpace.toLp μ hX.quadratic u))
    rw [hDs] at hmix
    have hi : (∫ x, SobolevSpace.toLp μ hX.quadratic w x * (ds k x) ^ 2 ∂μ) =
        ∫ x, v x * (ds k x) ^ 2 ∂μ := by
      apply integral_congr_ae
      exact hw.mono fun x hx => congrArg (fun a => a * (ds k x) ^ 2) hx
    rw [hi] at hmix
    change energyForm μ hX.quadratic (Gs k) w +
      2 * K * inner ℝ (SobolevSpace.toLp μ hX.quadratic w) (SobolevSpace.toLp μ hX.quadratic (Gs k)) +
      2 * weightedGamma μ hX.quadratic (SobolevSpace.toLp μ hX.quadratic w) (us k) (Ds k) ≤ 0 at hboch
    linarith
  have hlim := bochner_sobolev_limit μ hX.quadratic M hus huM hconv hdconv hGsΓ hG
    hB hE w hv C hvb K hb
  linarith

theorem NoncollapsedRCD.compact_bochner_test {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (u : SobolevSpace (hausdorff n X) hX.quadratic)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] φ)
    (d : Lp ℝ 2 (hausdorff n X)) (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (G : SobolevSpace (hausdorff n X) hX.quadratic)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic u u)
    (w : SobolevSpace (hausdorff n X) hX.quadratic) {v : X → ℝ} {A : ℝ≥0}
    (hv : LipschitzWith A v) (hw : SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[hausdorff n X] v)
    (C : ℝ≥0) (hvb : ∀ x, |v x| ≤ C) (hv0 : ∀ x, 0 ≤ v x) :
    0 ≤ -(1 / 2 : ℝ) * energyForm (hausdorff n X) hX.quadratic G w -
      K * inner ℝ (SobolevSpace.toLp (hausdorff n X) hX.quadratic w)
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic G) +
      (∫ x, v x * (d x) ^ 2 ∂hausdorff n X) +
      weightedGamma (hausdorff n X) hX.quadratic d u w := by
  exact hX.compact_bochner_sobolev_test hn hφ hs p u hu d hd G hG w
    hv.continuous.measurable hw C hvb hv0

end RegularPointCoordinates

end

end OAI
