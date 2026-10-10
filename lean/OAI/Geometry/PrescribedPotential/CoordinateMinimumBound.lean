import Mathlib
import OAI.Geometry.PrescribedPotential.ABPIntegralBound
import OAI.Geometry.PrescribedPotential.CoordinateBalls
import OAI.Geometry.PrescribedPotential.CoordinateEllipticity
import OAI.Geometry.PrescribedPotential.CoordinateExtension
import OAI.Geometry.PrescribedPotential.CoordinateInnerCover

namespace OAI

/-! Coordinate Minimum Bound. -/

section

 

noncomputable section
open Set Metric Filter Topology MeasureTheory Matrix
open scoped ContDiff InnerProductSpace ComplexOrder
namespace Anticanonical.SourceSmooth
open EllipticKernel PotentialABP
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local instance coordinateMinimumRealIP (d : ℕ) : InnerProductSpace ℝ (EC d) :=
  InnerProductSpace.rclikeToReal ℂ (EC d)
namespace CoordinateBall
variable [MeasurableSpace X] [BorelSpace X] (p : CoordinateBall A)

lemma minimum_bound (g : KaehlerMetric A) (B : ℝ) {K : ℝ} (hK : 0 < K) :
    ∃ C : ℝ, ∀ φ : SmoothRealFunction A,
      (∀ x, φ.value x ≤ 0) → (∫ x, -φ.value x ∂p.measure) ≤ B →
      (∀ z ∈ closedBall p.center (3*p.radius),
        |(g.matrix p.index (coordinateEquiv d z) + φ.hessian p.index (coordinateEquiv d z)).det.re| ≤ K) →
      ∀ x ∈ p.half.source, (∀ y, φ.value x ≤ φ.value y) → -φ.value x ≤ C := by
  obtain ⟨δ,hδ,hδb⟩ := p.metric_lower_bound g
  let r := p.radius/2
  have hr : 0 < r := by dsimp only [r]; exact half_pos p.radius_pos
  let C := δ*r^2/2+B*((4:ℝ)^(2*d)*K^2)/volume.real (closedBall (0:EC d) (δ*r/2))
  refine ⟨C, ?_⟩
  intro φ hn hB hdet x hx hmin
  let c := A.euclideanChart p.index x
  have hcb : c ∈ ball p.center (p.radius/2) := hx.2
  have hsub := p.centered_small_closedBall_subset hcb
  have hball : ball p.center p.radius ⊆ closedBall p.center (3*p.radius) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith [p.radius_pos]))
  have hsub3 : closedBall c r ⊆ closedBall p.center (3*p.radius) := hsub.trans hball
  have he (z) (hz : z ∈ closedBall p.center (3*p.radius)) :
      p.coordExtension φ ((EuclideanSpace.equiv (Fin d) ℂ) z) =
        φ.value ((A.euclideanChart p.index).symm z) := by
    change p.coordExtension φ (coordinateEquiv d z) = _
    rw [p.coordExtension_apply, p.extension_eq φ hz]
  have hec : p.coordExtension φ ((EuclideanSpace.equiv (Fin d) ℂ) c) = φ.value x := by
    rw [he c (hsub3 (mem_closedBall_self hr.le)), (A.euclideanChart p.index).left_inv hx.1]
  have hi : IntegrableOn
      (fun z : EC d => -p.coordExtension φ ((EuclideanSpace.equiv (Fin d) ℂ) z))
      (ball p.center p.radius) volume := by
    exact (((p.coordExtension_smooth φ).continuous.comp
      (EuclideanSpace.equiv (Fin d) ℂ).continuous).neg.continuousOn.integrableOn_compact
        (isCompact_closedBall p.center p.radius)).mono_set ball_subset_closedBall
  have hBi : (∫ z in ball p.center p.radius,
      -p.coordExtension φ ((EuclideanSpace.equiv (Fin d) ℂ) z)) ≤ B := by
    rw [p.integral_measure (fun x => -φ.value x) φ.continuous.neg] at hB
    apply (setIntegral_congr_fun isOpen_ball.measurableSet (fun z hz => ?_)).trans_le hB
    rw [he z (hball hz)]
  have hh := abp_integral_minimum_bound volume (p.coordExtension_smooth φ)
    (fun z => g.matrix p.index (coordinateEquiv d z)) hr hδ hK
    (by intro z hz; rw [hec, he z (hsub3 hz)]; exact hmin _)
    (by
      intro z hz
      apply (g.positive _ _ ?_).isHermitian
      have ht := p.closure_sub (closedBall_subset_closedBall (by linarith [p.radius_pos]) (hsub3 hz))
      simpa only [ComplexAtlas.euclideanChart_target, mem_preimage] using ht)
    (fun z hz v => hδb z (hsub3 hz) v)
    (by
      intro z hz
      change |(g.matrix p.index (coordinateEquiv d z) +
        PotentialKaehler.potentialMatrix (p.coordExtension φ) (coordinateEquiv d z)).det.re| ≤ K
      rw [p.coordExtension_hessian φ (hsub3 hz)]
      exact hdet z (hsub3 hz))
    isOpen_ball.measurableSet hsub
    (by intro z hz; rw [he z (hball hz)]; exact hn _) hi hBi
  rw [hec] at hh
  exact hh
end CoordinateBall
end Anticanonical.SourceSmooth

end
end

end OAI
