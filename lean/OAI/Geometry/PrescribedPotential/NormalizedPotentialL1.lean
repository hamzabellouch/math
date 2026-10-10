import Mathlib
import OAI.Geometry.PrescribedPotential.CompactIntegralPropagation
import OAI.Geometry.PrescribedPotential.CoordinateBalls
import OAI.Geometry.PrescribedPotential.CoordinatePotential
import OAI.Geometry.PrescribedPotential.QuasiPSHLocalMean

namespace OAI

/-! Normalized Potential L1. -/

section

 

noncomputable section
open Set Metric Filter Topology MeasureTheory
open scoped ContDiff InnerProductSpace
namespace Anticanonical.SourceSmooth
open EllipticKernel PotentialABP
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local instance normalizedL1RealIP (d : ℕ) : InnerProductSpace ℝ (EC d) :=
  InnerProductSpace.rclikeToReal ℂ (EC d)
namespace CoordinateBall
variable [MeasurableSpace X] [BorelSpace X] (p : CoordinateBall A)

lemma local_neg_integral (g : KaehlerMetric A) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ φ : SmoothRealFunction A, g.PositivePotential φ → (∀ x, φ.value x ≤ 0) →
    ∀ y ∈ p.source, (∫ x, -φ.value x ∂p.measure) ≤ B * (-φ.value y + 1) := by
  obtain ⟨C, hC, hCb⟩ := p.metric_bound g
  let V := volume.real (ball (0 : EC d) (2*p.radius))
  let T := 9*C*p.radius^2
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hT : 0 ≤ T := by positivity
  refine ⟨V*(1+T), mul_nonneg hV (by positivity), ?_⟩
  intro φ hφ hneg y hy
  have he (z) (hz : z ∈ closedBall p.center (3*p.radius)) := p.extension_eq φ hz
  have hloc := quasiPSH_local_integral (p.extension_smooth φ) p.center p.radius_pos hC
    (fun z hz => by rw [he z hz]; exact hneg _) (fun z hz v => p.extension_levi_lower g φ hφ hCb hz v)
    (y := A.euclideanChart p.index y) hy.2
  have hey : p.extension φ (A.euclideanChart p.index y) = φ.value y := by
    rw [he _ (closedBall_subset_closedBall (by linarith [p.radius_pos])
      (ball_subset_closedBall hy.2)), (A.euclideanChart p.index).left_inv hy.1]
  have hei : (∫ z in ball p.center p.radius, (0:ℝ)-p.extension φ z) =
      ∫ z in ball p.center p.radius, -φ.value ((A.euclideanChart p.index).symm z) := by
    apply setIntegral_congr_fun isOpen_ball.measurableSet
    intro z hz
    dsimp only
    rw [he z (closedBall_subset_closedBall (by linarith [p.radius_pos])
      (ball_subset_closedBall hz)), zero_sub]
  rw [hei, hey, zero_sub] at hloc
  rw [p.integral_measure (fun x => -φ.value x) φ.continuous.neg]
  apply hloc.trans
  change V * (-φ.value y + T) ≤ V*(1+T)*(-φ.value y+1)
  have hn : 0 ≤ -φ.value y := neg_nonneg.mpr (hneg y)
  nlinarith [mul_nonneg hT hn, mul_nonneg hV (mul_nonneg hT hn)]
end CoordinateBall

 

theorem normalized_potential_L1 [CompactSpace X] [ConnectedSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (g : KaehlerMetric A) (S : Finset (CoordinateBall A))
    (hS : ∀ x, ∃ p ∈ S, x ∈ p.source) :
    ∃ B : ℝ, ∀ φ : SmoothRealFunction A,
      g.PositivePotential φ → (∀ x, φ.value x ≤ 0) → (∃ x, φ.value x = 0) →
      ∀ p ∈ S, (∫ x, -φ.value x ∂p.measure) ≤ B := by
  classical
  let U : S → Set X := fun p => p.val.source
  let μ : S → Measure X := fun p => p.val.measure
  let F : (X → ℝ) → Prop := fun u => ∃ φ : SmoothRealFunction A,
    g.PositivePotential φ ∧ (∀ x, φ.value x ≤ 0) ∧ u = fun x => -φ.value x
  have hlocal := fun p : S => p.val.local_neg_integral g
  choose C hC hc using hlocal
  obtain ⟨B, hB⟩ := finite_cover_integral_bound U
    (fun p => p.val.isOpen_source) (fun p => p.val.source_nonempty)
    (fun x => by obtain ⟨p, hp, hx⟩ := hS x; exact ⟨⟨p, hp⟩, hx⟩) μ
    (fun p q hn => p.val.measure_open_pos q.val.isOpen_source hn) F
    (by rintro u ⟨φ, _, hn, rfl⟩ x; exact neg_nonneg.mpr (hn x))
    (by
      rintro u ⟨φ, _, _, rfl⟩ p
      exact φ.continuous.neg.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) C hC
    (by rintro u ⟨φ, hφ, hn, rfl⟩ p y hy; exact hc p φ hφ hn y hy)
  refine ⟨B, ?_⟩
  intro φ hφ hn hz p hp
  exact hB _ ⟨φ, hφ, hn, rfl⟩ (by obtain ⟨x, hx⟩ := hz; exact ⟨x, by simp [hx]⟩) ⟨p, hp⟩
end Anticanonical.SourceSmooth

end
end

end OAI
