import OAI.Geometry.RCD.Sobolev.CenteredHarmonicEnergy
import OAI.Geometry.RCD.Sobolev.ContinuousLocalGradientBound
import OAI.Geometry.RCD.Harmonic.FirstOrderLocalization

namespace OAI

/-! # Bounded centered harmonic components of a first-order frame -/

open Set Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.centered_first_order_frame {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) {p : X} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n)
    (hsplit : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (80*r) ε u v) :
    ∃ w : Fin n → SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p (5*r)) (w i)) ∧
      (∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i) =ᵐ[
        (hausdorff n X).restrict (ball p (5*r))] fun x => (r⁻¹ • (v x-v p)) i) ∧
      (∀ i, harmonicTargetNorm hX p (5*r) (w i) ≤ 10) ∧
      ∀ i j, (fun x => r^2*localGamma (hausdorff n X) hX.quadratic (w i) (w j) x) =ᵐ[
        (hausdorff n X).restrict (ball p (5*r))]
        localGamma (hausdorff n X) hX.quadratic (u i) (u j) := by
  let μ := hausdorff n X
  have hs40 : ball p (8*(5*r)) ⊆ ball p (80*r) := ball_subset_ball (by linarith)
  have hs5 : ball p (5*r) ⊆ ball p (80*r) := ball_subset_ball (by linarith)
  have hex (i : Fin n) := hX.centered_harmonic_direction_with_energy hn p
    (show 0<5*r by positivity) hr (by norm_num : (0:ℝ)≤10) (u i)
    (fun x => v x i) (v p i) ((hsplit.harmonic i).mono μ hX.quadratic hs5)
    (ae_restrict_of_ae_restrict_of_subset hs5 (hsplit.representative i))
  have hb (i : Fin n) : ∀ x ∈ ball p (5*r), |v x i-v p i| ≤ 10*r := by
    have hg : ∀ᵐ x ∂μ.restrict (ball p (8*(5*r))),
        localGamma μ hX.quadratic (u i) (u i) x ≤ ((2 : ℝ≥0) : ℝ)^2 := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hs40 (hsplit.gradient i)] with x hx
      norm_num only [NNReal.coe_ofNat] at *
      nlinarith
    have hv : ContinuousOn (fun x => v x i) (ball p (8*(5*r))) :=
      (EuclideanSpace.proj i).continuous.comp_continuousOn (hsplit.continuous.mono hs40)
    have hbound := hX.continuous_local_gradient_bound hn (u i) (fun x => v x i) p
      (show 0<5*r by positivity) 2 hv
      (ae_restrict_of_ae_restrict_of_subset hs40 (hsplit.representative i)) hg
    intro x hx
    have hh := hbound x hx
    norm_num only [NNReal.coe_ofNat] at hh
    have hd : dist x p < 5*r := hx
    linarith
  choose w hw hrep hnorm he using (fun i => hex i (hb i))
  refine ⟨w,hw,?_,hnorm,?_⟩
  · intro i
    filter_upwards [hrep i] with x hx
    change _ = r⁻¹*(v x i-v p i)
    simpa only [div_eq_inv_mul] using hx
  · intro i j
    exact rescaled_local_pairing_of_centering μ hX.quadratic (ball p (5*r)) hr.ne'
      (u i) (u j) (w i) (w j) (he i) (he j)

end RegularPointCoordinates

end

end OAI
