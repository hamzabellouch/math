import OAI.Geometry.RCD.Harmonic.HarmonicContinuousRepresentative
import OAI.Geometry.RCD.Harmonic.FirstOrderLocalization

namespace OAI

/-! # Packaging an actual scaled harmonic family as a first-order splitting map -/

open Set Metric Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_splitting_of_scaled_family {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (p : X) {r β : ℝ} (hr : 0 < r) (hβ : 0<β) (hcurv : -1≤K*(5*r)^2)
    (w : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (5*r)) (w i))
    (hnorm : ∀ i, harmonicTargetNorm hX p (5*r) (w i)≤7)
    (hgrad : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (3*r)),
      r^2*localGamma (hausdorff n X) hX.quadratic (w i) (w i) x≤1+β)
    (hgram : ∀ i j, ((hausdorff n X).real (ball p (2*r)))⁻¹*
      ∫ x in ball p (2*r),
        |r^2*localGamma (hausdorff n X) hX.quadratic (w i) (w j) x-(if i=j then 1 else 0)|
        ∂hausdorff n X≤β) :
    ∃ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*r) β u v := by
  classical
  let μ := hausdorff n X
  choose c hc hrep using fun i => hX.harmonic_continuous_representative hn p hr hcurv (w i) (hw i) (hnorm i)
  let u := fun i => r • w i
  let v : X → Euclidean n := fun x => WithLp.toLp 2 (fun i => r*c i x)
  have hGamma (i j : Fin n) : localGamma μ hX.quadratic (u i) (u j) =ᵐ[μ]
      fun x => r^2*localGamma μ hX.quadratic (w i) (w j) x := by
    filter_upwards [localGamma_smul_left μ hX.quadratic r (w i) (u j),
      localGamma_smul_right μ hX.quadratic r (w i) (w j)] with x hl hr'
    change localGamma μ hX.quadratic (r • w i) (u j) x=_
    rw [hl,hr']
    ring
  refine ⟨u,v,?_,?_,?_,?_,?_⟩
  · intro i
    have hu : SobolevSpace.toLp μ hX.quadratic (u i) =ᵐ[μ]
        fun x => r*SobolevSpace.toLp μ hX.quadratic (w i) x := by
      dsimp only [u]
      rw [map_smul]
      exact Lp.coeFn_smul _ _
    filter_upwards [ae_restrict_of_ae hu,hrep i] with x hx hi
    change SobolevSpace.toLp μ hX.quadratic (u i) x=r*c i x
    rw [hx,hi]
  · exact ((PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
      (continuous_pi (fun i => continuous_const.mul (hc i)))).continuousOn
  · intro i
    exact ((hw i).mono μ hX.quadratic
      (ball_subset_ball (by linarith : 2*r≤5*r))).smul μ hX.quadratic r
  · intro i
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith : 2*r≤3*r)) (hgrad i),ae_restrict_of_ae (hGamma i i)] with x hx he
    rw [he]
    nlinarith
  · intro i j
    convert hgram i j using 1
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (hGamma i j)] with x hx
    rw [hx]

end RegularPointCoordinates

end

end OAI
