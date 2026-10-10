import OAI.Geometry.RCD.Harmonic.BoundedHarmonicValueLimit
import OAI.Geometry.RCD.Metric.ExpandingPointedValueLimit

namespace OAI

/-! # Harmonic identification of the common expanding-domain value limit -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.expanding_harmonic_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) (u : ℕ → X → ℝ)
    (w : ℕ → ℕ → SobolevSpace (hausdorff n X) hX.quadratic) (M : ℕ → ℝ)
    (hM : ∀ m, 0 < M m)
    (hdata : ∀ m : ℕ, ∀ᶠ k in atTop, -1 ≤ K*(r k)^2 ∧
      IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k)
        ((m : ℝ)+1) (ε k) (V k) ∧
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
        (ball (p k) (((m : ℝ)+1)*r k)) (w m k) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic (w m k) =ᵐ[
        (hausdorff n X).restrict (ball (p k) (((m : ℝ)+1)*r k))] u k) ∧
      harmonicTargetNorm hX (p k) (((m : ℝ)+1)*r k) (w m k) ≤ M m)
    (f : Euclidean n → ℝ) (hfc : Continuous f)
    (hfL : ∀ ρ : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L f (closedBall 0 ρ))
    (hconv : ∀ W : ℝ, 0 < W → ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ∀ x, dist x (p k) ≤ W*r k → |u k x-f (V k x)| < η) :
    InnerProductSpace.HarmonicOnNhd f univ := by
  have hlocal (m : ℕ) : InnerProductSpace.HarmonicOnNhd f (ball 0 ((m : ℝ)+1)) := by
    obtain ⟨N,hN⟩ := eventually_atTop.1 (hdata m)
    let b : ℕ → ℕ := fun k => k+N
    have hb : Tendsto b atTop atTop := tendsto_add_atTop_nat N
    have hd (k : ℕ) := hN (b k) (Nat.le_add_left N k)
    apply hX.bounded_harmonic_value_limit hn (by positivity) (hM m)
      (p∘b) (r∘b) (ε∘b) (V∘b) (fun k => hr (b k)) (fun k => (hd k).1)
      (fun k => hε (b k)) (fun k => hε1 (b k)) (hεlim.comp hb)
      (fun k => (hd k).2.1) (fun k => w m (b k))
      (fun k => (hd k).2.2.1) (fun k => (hd k).2.2.2.2) f hfc.continuousOn
      (fun W _ => hfL W)
    intro W hW hWS η hη
    filter_upwards [hb.eventually (hconv W hW η hη)] with k hk
    have hs : ball (p (b k)) (W*r (b k)) ⊆
        ball (p (b k)) (((m : ℝ)+1)*r (b k)) :=
      ball_subset_ball (mul_le_mul_of_nonneg_right hWS.le (hr (b k)).le)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs (hd k).2.2.2.1,
      ae_restrict_mem measurableSet_ball] with x hx hball
    rw [hx]
    exact (hk x (show dist x (p (b k)) ≤ W*r (b k) from hball.le)).le
  intro z _
  obtain ⟨m,hm⟩ := exists_nat_gt ‖z‖
  apply hlocal m z
  simp only [mem_ball,dist_zero_right]
  linarith

end RegularPointCoordinates

end

end OAI
