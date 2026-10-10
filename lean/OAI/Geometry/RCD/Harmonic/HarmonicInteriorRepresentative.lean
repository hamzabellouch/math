import OAI.Geometry.RCD.Harmonic.HarmonicInteriorMean
import OAI.Geometry.RCD.Sobolev.InteriorBoundedGradientRepresentative
import OAI.Geometry.RCD.Sobolev.HarmonicGradientInput

namespace OAI

/-! # Uniform harmonic representatives on arbitrary strict interior balls -/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem harmonic_interior_bounded_representative {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    (hmean : LocalHarmonicL2MeanValueInput hX) (hgradient : LocalHarmonicL2GradientInput hX)
    {a τ : ℝ} (ha : 0≤a) (hτ : 0<τ) (hτ1 : τ<1) :
    ∃ C : ℝ, 1≤C ∧ ∀ (p : X) (R : ℝ), 0<R → -a≤K*R^2 →
      ∀ u : SobolevSpace (hausdorff n X) hX.quadratic,
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) u →
      harmonicTargetNorm hX p R u ≤ 1 →
      ∃ v : X → ℝ, LipschitzWith (C/R).toNNReal v ∧ (∀ x, |v x|≤C) ∧
        SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[
          (hausdorff n X).restrict (ball p (τ*R))] v := by
  let σ := (τ+1)/2
  let θ := (σ+1)/2
  let δ := σ-τ
  have hτσ : τ<σ := by dsimp only [σ]; linarith
  have hσθ : σ<θ := by dsimp only [σ,θ]; linarith
  have hθ : 0<θ := by dsimp only [σ,θ]; linarith
  have hθ1 : θ<1 := by dsimp only [σ,θ]; linarith
  have hδ : 0<δ := sub_pos.mpr hτσ
  obtain ⟨M,hM,hmb⟩ := harmonic_interior_mean_bound hX hn hmean ha hθ hθ1
  obtain ⟨G,hG,hgb⟩ := hgradient hn a θ ha hθ hθ1
  have hM0 : 0≤M := zero_le_one.trans hM
  have hG0 : 0≤G := zero_le_one.trans hG
  have hMd : 0≤M/δ := div_nonneg hM0 hδ.le
  let C := 2*G+2*(M/δ)+M
  have hC : 1≤C := by dsimp only [C]; linarith
  have hC0 : 0≤C := zero_le_one.trans hC
  refine ⟨C,hC,?_⟩
  intro p R hR hcurv u hu hnorm
  let μ := hausdorff n X
  have hm : ∀ᵐ x ∂μ.restrict (ball p (θ*R)), |SobolevSpace.toLp μ hX.quadratic u x|≤M := by
    filter_upwards [hmb p R hR hcurv u hu] with x hx
    exact hx.trans (by nlinarith only [mul_le_mul_of_nonneg_left hnorm hM0])
  have hmeansq := sobolev_mean_sq_le_one_of_normalized μ hX.quadratic (ball p R)
    (hX.finiteOnBounded _ isBounded_ball).ne u hnorm
  have hgrad : ∀ᵐ x ∂μ.restrict (ball p (θ*R)),
      SobolevSpace.minimalSlope μ hX.quadratic u x≤G/R := by
    filter_upwards [hgb p R hR hcurv u hu,
      ae_restrict_of_ae (localGamma_self μ hX.quadratic u)] with x hx he
    rw [he] at hx
    have hb := hx.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hmeansq (sq_nonneg (G/R)))
    have hp : 0≤G/R := div_nonneg hG0 hR.le
    nlinarith [sq_nonneg (SobolevSpace.minimalSlope μ hX.quadratic u x-G/R)]
  rw [ae_restrict_iff' measurableSet_ball] at hm hgrad
  have hloc (x : X) (hx : dist p x≤σ*R) : x∈ball p (θ*R) := by
    change dist x p<θ*R
    rw [dist_comm]
    nlinarith
  obtain ⟨v,hv,hvM,hvrep⟩ := hX.interior_bounded_gradient_representative K n hn u p
    (τ*R) (σ*R) (mul_lt_mul_of_pos_right hτσ hR)
    ⟨G/R,div_nonneg hG0 hR.le⟩ ⟨M,hM0⟩
    (hm.mono fun x hx hdist => hx (hloc x hdist))
    (hgrad.mono fun x hx hdist => hx (hloc x hdist))
  refine ⟨v,hv.weaken ?_,fun x => (hvM x).trans ?_,hvrep⟩
  · change Real.sqrt (2*(G/R)^2+2*M^2*((σ*R-τ*R)⁻¹)^2)≤(C/R).toNNReal
    rw [Real.coe_toNNReal _ (div_nonneg hC0 hR.le)]
    apply Real.sqrt_le_iff.mpr
    refine ⟨div_nonneg hC0 hR.le,?_⟩
    have hgap : σ*R-τ*R=δ*R := by dsimp only [δ]; ring
    rw [hgap]
    have hb : 2*G^2+2*(M/δ)^2≤C^2 := by
      dsimp only [C]
      nlinarith [mul_nonneg hG0 hMd,mul_nonneg hG0 hM0,
        mul_nonneg hMd hM0,sq_nonneg G,sq_nonneg (M/δ),sq_nonneg M]
    convert div_le_div_of_nonneg_right hb (sq_nonneg R) using 1 <;> ring_nf
  · change M≤C
    dsimp only [C]
    linarith

end RegularPointCoordinates

end

end OAI
