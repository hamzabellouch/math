import OAI.Geometry.RCD.Coordinates.AffineFitPerturbation

namespace OAI

/-! # The two-scale affine-fit estimate from an actual harmonic correction -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)

/-- Harmonic improvement and a harmonic correction give the one-step fit
estimate for a possibly nonharmonic L² target. The error is the actual
correction norm and the restriction loss is the actual volume ratio. -/
theorem harmonic_affine_fit_step
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (p : X) {r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hu : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) (u i))
    (η : SobolevSpace (hausdorff n X) hX.quadratic)
    (hη : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) η)
    (hηone : SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p r) η =
      restrictedOne (hausdorff n X) (ball p r) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)))
    (hfit : HasNormalizedAffineImprovement hX u p r θ)
    (f : Lp ℝ 2 ((hausdorff n X).restrict (ball p r)))
    (h : SobolevSpace (hausdorff n X) hX.quadratic)
    (hh : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) h) :
    let μ := hausdorff n X
    let hs := ne_of_lt (hX.finiteOnBounded (ball p r) isBounded_ball)
    let ht := ne_of_lt (hX.finiteOnBounded (ball p (θ * r)) isBounded_ball)
    let hsub := ball_subset_ball (mul_le_of_le_one_left hr.le hθ1)
    let C := (1 / 2 : ℝ) * θ * Real.sqrt θ
    let D := Real.sqrt (μ.real (ball p r)) / Real.sqrt (μ.real (ball p (θ * r)))
    ‖normalizeLocalL2 μ (ball p (θ * r)) ht
      (affineResidual μ hX.quadratic u (ball p (θ * r)) ht
        (localL2Restriction μ (ball p r) (ball p (θ * r)) hsub f))‖ ≤
      (D + C) * ‖normalizeLocalL2 μ (ball p r) hs
        (f - SobolevSpace.restrictLp μ hX.quadratic (ball p r) h)‖ +
      C * ‖normalizeLocalL2 μ (ball p r) hs (affineResidual μ hX.quadratic u (ball p r) hs f)‖ := by
  let μ := hausdorff n X
  let s := ball p r
  let t := ball p (θ * r)
  let hs : μ s ≠ ∞ := ne_of_lt (hX.finiteOnBounded _ isBounded_ball)
  let ht : μ t ≠ ∞ := ne_of_lt (hX.finiteOnBounded _ isBounded_ball)
  have hsub : t ⊆ s := ball_subset_ball (mul_le_of_le_one_left hr.le hθ1)
  let R := localL2Restriction μ s t hsub
  let Ns := fun g : Lp ℝ 2 (μ.restrict s) => ‖normalizeLocalL2 μ s hs g‖
  let Nt := fun g : Lp ℝ 2 (μ.restrict t) => ‖normalizeLocalL2 μ t ht g‖
  let C := (1 / 2 : ℝ) * θ * Real.sqrt θ
  let D := Real.sqrt (μ.real s) / Real.sqrt (μ.real t)
  let hsval := SobolevSpace.restrictLp μ hX.quadratic s h
  let htval := SobolevSpace.restrictLp μ hX.quadratic t h
  let Ps := affineProjection μ hX.quadratic u s hs
  let Es := affineResidual μ hX.quadratic u s hs
  let Et := affineResidual μ hX.quadratic u t ht
  change Nt (Et (R f)) ≤ (D + C) * Ns (f - hsval) + C * Ns (Es f)
  obtain ⟨F, c, v, hF, hFharm, hFs⟩ := affineProjection_harmonic_representative μ hX.quadratic
    u s hs hu η hη hηone f
  have hFs' : SobolevSpace.restrictLp μ hX.quadratic s F =
      affineCoordinateMap μ hX.quadratic u s hs (c, v) := by
    rw [hF, map_add, map_smul, hηone, affineCoordinateMap_apply]
  have hFt : SobolevSpace.restrictLp μ hX.quadratic t F =
      affineCoordinateMap μ hX.quadratic u t ht (c, v) := by
    rw [← localL2Restriction_sobolev μ hX.quadratic s t hsub F, hFs',
      localL2Restriction_affine]
  have hHharm : IsSobolevHarmonicOn μ hX.quadratic s (h - F) := by
    simpa only [neg_one_smul, ← sub_eq_add_neg] using
      hh.add μ hX.quadratic (hFharm.smul μ hX.quadratic (-1))
  have himprove := hfit.homogeneous hX hr hθ1 (h - F) hHharm
  change Nt (Et (SobolevSpace.restrictLp μ hX.quadratic t (h - F))) ≤
    C * Ns (SobolevSpace.restrictLp μ hX.quadratic s (h - F)) at himprove
  rw [map_sub, hFt, affineResidual_sub_affine] at himprove
  have houter : Ns (SobolevSpace.restrictLp μ hX.quadratic s (h - F)) ≤
      Ns (Es f) + Ns (f - hsval) := by
    have he : SobolevSpace.restrictLp μ hX.quadratic s (h - F) = Es f - (f - hsval) := by
      rw [map_sub, hFs]
      change hsval - Ps f = (f - Ps f) - (f - hsval)
      abel
    rw [he]
    change ‖_ • (Es f - (f - hsval))‖ ≤ ‖_ • Es f‖ + ‖_ • (f - hsval)‖
    rw [smul_sub]
    exact norm_sub_le _ _
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hbound : Nt (Et htval) ≤ C * (Ns (Es f) + Ns (f - hsval)) :=
    himprove.trans (mul_le_mul_of_nonneg_left houter hC)
  have herr : Nt (R f - htval) ≤ D * Ns (f - hsval) := by
    have hrestrict := normalized_localL2Restriction_le μ s t hsub hs ht
      (ne_of_gt (hX.fullSupport p r hr)) (ne_of_gt (hX.fullSupport p (θ * r) (mul_pos hθ hr)))
      (f - hsval)
    have hRh : R hsval = htval := localL2Restriction_sobolev μ hX.quadratic s t hsub h
    have hmap : R (f - hsval) = R f - htval := by rw [map_sub, hRh]
    change Nt (R (f - hsval)) ≤ D * Ns (f - hsval) at hrestrict
    rwa [hmap] at hrestrict
  have hperturb := normalized_affineResidual_perturbation μ hX.quadratic u t ht (R f) htval
  change Nt (Et (R f)) ≤ Nt (R f - htval) + Nt (Et htval) at hperturb
  nlinarith

end RegularPointCoordinates

end

end OAI
