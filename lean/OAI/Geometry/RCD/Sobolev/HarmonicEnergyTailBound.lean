import OAI.Geometry.RCD.Sobolev.RCDPoissonEnergySubsolution
import OAI.Geometry.RCD.Sobolev.SubsolutionUpperTailGap

namespace OAI

/-! # Sharp local harmonic gradient bounds from a small energy tail -/

open Set Metric Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_energy_small_tail_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (β : ℝ) (hβ : 0<β) :
    ∃ δ : ℝ, 0<δ ∧ ∀ (p : X) (r s : ℝ), 0 < r → 0 ≤ s → -1 ≤ K*(2*r)^2 →
      ∀ (f : SobolevSpace (hausdorff n X) hX.quadratic) (L : ℝ≥0),
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (8*r)) f →
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
        localGamma (hausdorff n X) hX.quadratic f f x≤(L:ℝ)^2) →
      (∫ x in ball p (2*r), (max (s*localGamma (hausdorff n X) hX.quadratic f f x-1) 0)^2
        ∂hausdorff n X)≤δ*(hausdorff n X).real (ball p (2*r)) →
      ∀ᵐ x ∂(hausdorff n X).restrict (ball p r),
        s*localGamma (hausdorff n X) hX.quadratic f f x≤1+β := by
  obtain ⟨δ,hδ,hbound⟩ := hX.subsolution_upper_tail_gap hn 2 1 β (by norm_num) zero_le_one hβ
  refine ⟨δ,hδ,?_⟩
  intro p r s hr hs hcurv f L hf hgrad hsmall
  let μ := hausdorff n X
  obtain ⟨e,B,hB,he,_,hsub⟩ := hX.poisson_energy_subsolution hn p hr f 0 L
    ((isConstantLaplacianOn_zero_iff μ hX.quadratic _ _).mpr hf) hgrad
  let v := s • e
  have hv : SobolevSpace.toLp μ hX.quadratic v =ᵐ[μ.restrict (ball p (2*r))]
      fun x => s*localGamma μ hX.quadratic f f x := by
    have hrep : SobolevSpace.toLp μ hX.quadratic v =ᵐ[μ]
        fun x => s*SobolevSpace.toLp μ hX.quadratic e x := by
      dsimp only [v]
      rw [map_smul]
      exact Lp.coeFn_smul _ _
    filter_upwards [ae_restrict_of_ae hrep,he] with x hx hex
    rw [hx,hex]
  have haR : (2*max (-K) 0)*(2*r)^2≤2 := by
    by_cases hK : K≤0
    · rw [max_eq_left (neg_nonneg.mpr hK)]
      nlinarith
    · rw [max_eq_right (by linarith : -K≤0)]
      norm_num
  have hsmall' : (∫ x in ball p (2*r),
      (max (SobolevSpace.toLp μ hX.quadratic v x-1) 0)^2 ∂μ)≤δ*μ.real (ball p (2*r)) := by
    convert hsmall using 1
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    rw [hx]
  have hb := hbound p (2*r) (by positivity) hcurv v (2*max (-K) 0)
    (by positivity) haR (hsub.smul μ hX.quadratic s hs) hsmall'
  have hbr : (2*r)/2=r := by ring
  rw [hbr] at hb
  filter_upwards [hb,ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (by linarith : r≤2*r)) hv] with x hx hrep
  rwa [hrep] at hx

end RegularPointCoordinates

end

end OAI
