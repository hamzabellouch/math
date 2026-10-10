import OAI.Geometry.RCD.Coordinates.HarmonicFitStep
import OAI.Geometry.RCD.Harmonic.RadialDerivativeError

namespace OAI

/-! # Feeding an actual radial harmonic approximation into the affine fit -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)

/-- A proved integral error for the actual radial pairing yields its
least-squares contraction, with the exact restriction volume factor. -/
theorem radial_fit_of_harmonic_correction
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (p : X) {r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hu : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) (u i))
    (η : SobolevSpace (hausdorff n X) hX.quadratic)
    (hη : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) η)
    (hηone : SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p r) η =
      restrictedOne (hausdorff n X) (ball p r) (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)))
    (hfit : HasNormalizedAffineImprovement hX u p r θ)
    (q a h : SobolevSpace (hausdorff n X) hX.quadratic)
    {B error : ℝ} (he : 0 ≤ error)
    (ha : ∀ᵐ x ∂(hausdorff n X).restrict (ball p r),
      localGamma (hausdorff n X) hX.quadratic a a x ≤ B)
    (hh : IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) h)
    (herror : (∫ x in ball p r,
      (localGamma (hausdorff n X) hX.quadratic q a x -
        SobolevSpace.toLp (hausdorff n X) hX.quadratic h x) ^ 2 ∂hausdorff n X) ≤ error) :
    let μ := hausdorff n X
    let hs := ne_of_lt (hX.finiteOnBounded (ball p r) isBounded_ball)
    let ht := ne_of_lt (hX.finiteOnBounded (ball p (θ * r)) isBounded_ball)
    let hsub := ball_subset_ball (mul_le_of_le_one_left hr.le hθ1)
    let raw := (localGamma_memLp_two_of_bound μ hX.quadratic (ball p r) q a ha).toLp
      (localGamma μ hX.quadratic q a)
    let C := (1 / 2 : ℝ) * θ * Real.sqrt θ
    let V := Real.sqrt (μ.real (ball p r)) / Real.sqrt (μ.real (ball p (θ * r)))
    ‖normalizeLocalL2 μ (ball p (θ * r)) ht
      (affineResidual μ hX.quadratic u (ball p (θ * r)) ht
        (localL2Restriction μ (ball p r) (ball p (θ * r)) hsub raw))‖ ≤
      (V + C) * Real.sqrt ((μ.real (ball p r))⁻¹ * error) +
      C * ‖normalizeLocalL2 μ (ball p r) hs
        (affineResidual μ hX.quadratic u (ball p r) hs raw)‖ := by
  let μ := hausdorff n X
  let s := ball p r
  let hs : μ s ≠ ∞ := ne_of_lt (hX.finiteOnBounded _ isBounded_ball)
  let rawmem := localGamma_memLp_two_of_bound μ hX.quadratic s q a ha
  let raw := rawmem.toLp (localGamma μ hX.quadratic q a)
  let hlocal := SobolevSpace.restrictLp μ hX.quadratic s h
  have hnormsq : ‖normalizeLocalL2 μ s hs (raw - hlocal)‖ ^ 2 ≤ (μ.real s)⁻¹ * error := by
    rw [normalizeLocalL2_norm_sq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have heq : (fun x => ((raw - hlocal) x) ^ 2) =ᵐ[μ.restrict s]
        fun x => (localGamma μ hX.quadratic q a x - SobolevSpace.toLp μ hX.quadratic h x) ^ 2 := by
      filter_upwards [Lp.coeFn_sub raw hlocal, MemLp.coeFn_toLp rawmem,
        SobolevSpace.restrictLp_coe μ hX.quadratic s h] with x hsub hraw hloc
      simp only [hsub, Pi.sub_apply]
      exact congrArg (fun z : ℝ => z ^ 2) (congrArg₂ (fun x y : ℝ => x - y) hraw hloc)
    exact (integral_congr_ae heq).trans_le herror
  have hnorm : ‖normalizeLocalL2 μ s hs (raw - hlocal)‖ ≤ Real.sqrt ((μ.real s)⁻¹ * error) := by
    have hn : 0 ≤ (μ.real s)⁻¹ * error := by positivity
    nlinarith [Real.sq_sqrt hn, norm_nonneg (normalizeLocalL2 μ s hs (raw - hlocal)),
      Real.sqrt_nonneg ((μ.real s)⁻¹ * error)]
  have hstep := harmonic_affine_fit_step hX u p hr hθ hθ1 hu η hη hηone hfit raw h hh
  have hcoef : 0 ≤ Real.sqrt (μ.real (ball p r)) /
      Real.sqrt (μ.real (ball p (θ * r))) + (1 / 2 : ℝ) * θ * Real.sqrt θ := by positivity
  exact hstep.trans (add_le_add (mul_le_mul_of_nonneg_left hnorm hcoef) le_rfl)

end RegularPointCoordinates

end

end OAI
