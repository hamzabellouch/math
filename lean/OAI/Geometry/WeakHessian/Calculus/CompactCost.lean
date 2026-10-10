import Mathlib
import OAI.Geometry.WeakHessian.Entropy.DensityConvergence

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile9
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

lemma LipschitzWith.integrable_supported_ball {φ : X → ℝ} {L : ℝ≥0}
    (hφ : LipschitzWith L φ) {μ : Measure X} [IsFiniteMeasure μ]
    (o : X) (R : ℝ≥0) (hs : ∀ᵐ x ∂μ, x ∈ Metric.closedBall o R) : Integrable φ μ := by
  apply Integrable.of_bound hφ.continuous.aestronglyMeasurable (‖φ o‖+(L:ℝ)*R)
  filter_upwards [hs] with x hx
  have H := hφ.dist_le_mul x o
  have hd : dist x o ≤ R := hx
  calc
    ‖φ x‖ ≤ ‖φ o‖+‖φ x-φ o‖ := by simpa [add_comm, norm_sub_rev] using norm_le_norm_add_norm_sub (φ o) (φ x)
    _ ≤ _ := by rw [← dist_eq_norm]; exact add_le_add le_rfl (H.trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg))

lemma squareDensity_pairing_bound_supported {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf2 : MemLp f 2 m) (hg2 : MemLp g 2 m)
    [IsProbabilityMeasure (squareDensityMeasure m f)] [IsProbabilityMeasure (squareDensityMeasure m g)]
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (o : X) (R : ℝ≥0)
    (hsf : ∀ᵐ x ∂squareDensityMeasure m f, x ∈ Metric.closedBall o R)
    (hsg : ∀ᵐ x ∂squareDensityMeasure m g, x ∈ Metric.closedBall o R) :
    |(∫ x,φ x ∂squareDensityMeasure m f)-(∫ x,φ x ∂squareDensityMeasure m g)| ≤
      ((L:ℝ)*R)*(∫ x,|f x^2-g x^2| ∂m) := by
  let H : X → ℝ := (Metric.closedBall o R).indicator (fun x => φ x-φ o)
  have hHm : AEStronglyMeasurable H m :=
    (hφ.continuous.sub continuous_const).aestronglyMeasurable.indicator measurableSet_closedBall
  have hHb : ∀ x, ‖H x‖ ≤ (L:ℝ)*R := by
    intro x
    by_cases hx : x ∈ Metric.closedBall o R
    · rw [show H x = φ x-φ o from indicator_of_mem hx _]
      exact (hφ.dist_le_mul x o).trans (mul_le_mul_of_nonneg_left hx L.coe_nonneg)
    · simp only [H,indicator_of_notMem hx,norm_zero]; positivity
  have hI := squareDensity_pairing_bound hf hg hf2 hg2 hHm (ae_of_all _ hHb)
  have he (u : X → ℝ) [IsProbabilityMeasure (squareDensityMeasure m u)]
      (hs : ∀ᵐ x ∂squareDensityMeasure m u, x ∈ Metric.closedBall o R) :
      (∫ x,H x ∂squareDensityMeasure m u) = (∫ x,φ x ∂squareDensityMeasure m u)-φ o := by
    calc
      _ = ∫ x,φ x-φ o ∂squareDensityMeasure m u := integral_congr_ae (hs.mono fun x hx => indicator_of_mem hx _)
      _ = _ := by rw [integral_sub (LipschitzWith.integrable_supported_ball hφ o R hs) (integrable_const _)]; simp
  rw [he f hsf,he g hsg] at hI
  simpa only [sub_sub_sub_cancel_right] using hI

lemma planEnergy_le_of_contact {π η : Measure (Curve X)} [IsProbabilityMeasure π] [IsProbabilityMeasure η]
    (hbπ : BoundedTracks π) (hbη : BoundedTracks η)
    (_hiπ : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) π)
    (hiη : Integrable (fun γ : Curve X => dist (γ timeZero) (γ timeOne)^2) η)
    {φ ψ : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hψ : LipschitzWith T ψ)
    (hdual : ∀ x y,φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (h1 : interpolation π timeOne = interpolation η timeOne) :
    planEnergy π-planEnergy η ≤
      2*((∫ x,φ x ∂interpolation π timeZero)-(∫ x,φ x ∂interpolation η timeZero)) := by
  have hmap (p : Measure (Curve X)) (s : Time) (f : X → ℝ) (hf : Continuous f) :
      (∫ γ,f (γ s) ∂p) = ∫ x,f x ∂interpolation p s :=
    (integral_map (continuous_eval_const s).measurable.aemeasurable hf.aestronglyMeasurable).symm
  have hC : (∫ γ,φ (γ timeZero)+ψ (γ timeOne) ∂π) = planEnergy π/2 := by
    calc
      _ = ∫ γ,dist (γ timeZero) (γ timeOne)^2/2 ∂π := integral_congr_ae hcontact
      _ = _ := integral_div _ _
  have hB : (∫ γ,φ (γ timeZero)+ψ (γ timeOne) ∂η) ≤ planEnergy η/2 := by
    apply le_trans (integral_mono ((hbη.integrable_lipschitz_eval hφ timeZero).add
      (hbη.integrable_lipschitz_eval hψ timeOne)) (hiη.div_const 2) (fun γ => hdual _ _))
    exact le_of_eq (integral_div _ _)
  rw [integral_add (hbπ.integrable_lipschitz_eval hφ timeZero) (hbπ.integrable_lipschitz_eval hψ timeOne),
    hmap π timeZero φ hφ.continuous,hmap π timeOne ψ hψ.continuous,h1] at hC
  rw [integral_add (hbη.integrable_lipschitz_eval hφ timeZero) (hbη.integrable_lipschitz_eval hψ timeOne),
    hmap η timeZero φ hφ.continuous,hmap η timeOne ψ hψ.continuous] at hB
  linarith
end WeakHessian

end
end InlinedFile9

end OAI
