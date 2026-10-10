import OAI.Geometry.RCD.Sobolev.MeanPoincareInput

namespace OAI

/-! # The scalar forcing in the local Euler equation -/

open Set Metric MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Local Poincare turns the gradient estimate for Gamma(f,v)-v into
an actual scalar Euler equation with a constant and an L2 error. The error
has a global Sobolev representative, ready for the transport test. -/
theorem LocalMeanPoincareInput.euler_forcing {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    (hinput : LocalMeanPoincareInput hX) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (R : ℝ), 0 < R → -κ ≤ K * R ^ 2 →
      ∀ (f v G η : SobolevSpace (hausdorff n X) hX.quadratic),
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[
        (hausdorff n X).restrict (ball p R)] localGamma (hausdorff n X) hX.quadratic f v) →
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
        (hausdorff n X).restrict (ball p R)] fun _ => (1 : ℝ)) →
      ∃ (k : ℝ) (e : SobolevSpace (hausdorff n X) hX.quadratic),
        localGamma (hausdorff n X) hX.quadratic f v =ᵐ[
          (hausdorff n X).restrict (ball p R)]
          (fun x => SobolevSpace.toLp (hausdorff n X) hX.quadratic v x + k +
            SobolevSpace.toLp (hausdorff n X) hX.quadratic e x) ∧
        (∫ x in ball p R, (SobolevSpace.toLp (hausdorff n X) hX.quadratic e x) ^ 2
          ∂hausdorff n X) ≤ (C * R) ^ 2 *
            ∫ x in ball p (8 * R), localGamma (hausdorff n X) hX.quadratic (G - v) (G - v) x
              ∂hausdorff n X := by
  obtain ⟨C, hC, hP⟩ := hinput κ hκ
  refine ⟨C, hC, ?_⟩
  intro p R hR hcurv f v G η hG hη
  let μ := hausdorff n X
  let hQ := hX.quadratic
  obtain ⟨k, hk⟩ := hP p R hR hcurv (G - v)
  let e := (G - v) - k • η
  have hsub : SobolevSpace.toLp μ hQ (G - v) =ᵐ[μ]
      fun x => SobolevSpace.toLp μ hQ G x - SobolevSpace.toLp μ hQ v x := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  have he : SobolevSpace.toLp μ hQ e =ᵐ[μ.restrict (ball p R)]
      fun x => SobolevSpace.toLp μ hQ (G - v) x - k := by
    change SobolevSpace.toLp μ hQ ((G - v) - k • η) =ᵐ[_] _
    rw [map_sub, map_smul]
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ (G - v))
        (k • SobolevSpace.toLp μ hQ η)),
      ae_restrict_of_ae (Lp.coeFn_smul k (SobolevSpace.toLp μ hQ η)), hη] with x hs hm hηx
    rw [hs]
    simp only [Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul]
    change SobolevSpace.toLp μ hQ (G - v) x - k *
      SobolevSpace.toLp (hausdorff n X) hX.quadratic η x = _
    rw [hηx, mul_one]
  refine ⟨k, e, ?_, ?_⟩
  · filter_upwards [hG, he, ae_restrict_of_ae hsub] with x hg hx hs
    rw [hx, hs]
    change SobolevSpace.toLp μ hQ G x = localGamma μ hQ f v x at hg
    change localGamma μ hQ f v x = _
    linarith only [hg]
  · have hsquare : (fun x => (SobolevSpace.toLp μ hQ e x) ^ 2) =ᵐ[μ.restrict (ball p R)]
        fun x => (SobolevSpace.toLp μ hQ (G - v) x - k) ^ 2 := he.pow_const 2
    rw [integral_congr_ae hsquare]
    exact hk

end RegularPointCoordinates

end

end OAI
