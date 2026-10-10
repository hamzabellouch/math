import OAI.Geometry.RCD.Coordinates.GlobalFrameDefect
import OAI.Geometry.RCD.Harmonic.RadialDerivativeError

namespace OAI

/-! # Global energy defect of the actual local harmonic coordinate family -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_global_frame_defect {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hn : 2≤n) (hK : K≤0) (p : X)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    {R b : ℝ} (hR : 0<R) (hb : 4*R<b)
    (hH : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p b) (u i))
    (hL : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic (u i) (u i) x≤4)
    (g : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (q : Lp ℝ 2 (hausdorff n X)) (hq : IsWeakLaplacian (hausdorff n X) hX.quadratic g.val q)
    (d : SobolevSpace (hausdorff n X) hX.quadratic) (A : ℝ≥0)
    (hd : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic d x|≤A)
    (hqr : q =ᵐ[(hausdorff n X).restrict (ball p (2*R))]
      SobolevSpace.toLp (hausdorff n X) hX.quadratic d) :
    ∀ᵐ x ∂(hausdorff n X).restrict (ball p R),
      (localGamma (hausdorff n X) hX.quadratic g.val g.val x-
        ∑ i, (localGamma (hausdorff n X) hX.quadratic (u i) g.val x)^2)^2≤
      frameDefectConstant n*gramDefect (hausdorff n X) hX.quadratic u x*
        (localGamma (hausdorff n X) hX.quadratic g.val g.val x)^2 := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  have hsmall := hX.harmonic_gram_energy_defect hn hK p u hR hb hH hL g q hq d A hd hqr
  have hsub : ball p R⊆ball p b := ball_subset_ball (by linarith)
  have hc (i : Fin n) : ∀ᵐ x ∂μ.restrict (ball p R),
      (localGamma μ hQ (u i) g.val x)^2≤4*localGamma μ hQ g.val g.val x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hL i),
      ae_restrict_of_ae (localGamma_sq_le μ hQ (u i) g.val),
      ae_restrict_of_ae (localGamma_self μ hQ g.val)] with x hx hcs hg
    apply hcs.trans
    exact mul_le_mul_of_nonneg_right hx (by rw [hg]; positivity)
  filter_upwards [hsmall,ae_all_iff.mpr hc,
    ae_restrict_of_ae (localGamma_self μ hQ g.val)] with x hx hc hg
  have hg0 : 0≤localGamma μ hQ g.val g.val x := by rw [hg]; positivity
  apply frame_energy_defect_global hg0 (gramDefect_nonneg μ hQ u x)
    (fun i => localGamma μ hQ (u i) g.val x) hc
  change 5*gramDefect μ hQ u x≤1 →
    |localGamma μ hQ g.val g.val x-∑ i, (localGamma μ hQ (u i) g.val x)^2|≤
      Real.sqrt (30*gramDefect μ hQ u x)*|localGamma μ hQ g.val g.val x| at hx
  simpa only [abs_of_nonneg hg0] using hx

end RegularPointCoordinates

end

end OAI
