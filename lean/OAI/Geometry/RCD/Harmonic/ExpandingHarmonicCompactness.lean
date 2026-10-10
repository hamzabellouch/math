import OAI.Geometry.RCD.Harmonic.ExpandingHarmonicLimit

namespace OAI

/-! # Entire harmonic limits from actual local Sobolev families -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.expanding_harmonic_compactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) (u : ℕ → X → ℝ)
    (w : ℕ → ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (L : ℕ → ℝ≥0) (A M : ℕ → ℝ) (hA : ∀ m, 0 ≤ A m) (hM : ∀ m, 0 < M m)
    (hdata : ∀ m : ℕ, ∀ᶠ k in atTop, -1 ≤ K*(r k)^2 ∧
      IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k)
        ((m : ℝ)+1) (ε k) (V k) ∧
      IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
        (ball (p k) (((m : ℝ)+1)*r k)) (w m k) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic (w m k) =ᵐ[
        (hausdorff n X).restrict (ball (p k) (((m : ℝ)+1)*r k))] u k) ∧
      harmonicTargetNorm hX (p k) (((m : ℝ)+1)*r k) (w m k) ≤ M m ∧
      (∀ x, dist x (p k) ≤ ((m : ℝ)+1)*r k → |u k x| ≤ A m) ∧
      (∀ x y, dist x (p k) ≤ ((m : ℝ)+1)*r k → dist y (p k) ≤ ((m : ℝ)+1)*r k →
        |u k x-u k y| ≤ (L m : ℝ)*(dist x y/r k))) :
    ∃ (a : ℕ → ℕ) (f : Euclidean n → ℝ), StrictMono a ∧ Continuous f ∧
      InnerProductSpace.HarmonicOnNhd f univ ∧
      (∀ ρ : ℝ, ∃ C : ℝ≥0, LipschitzOnWith C f (closedBall 0 ρ)) ∧
      ∀ W : ℝ, 0 < W → ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ x,
        dist x (p (a k)) ≤ W*r (a k) → |u (a k) x-f (V (a k) x)| < η := by
  obtain ⟨a,f,ha,hfc,hfL,hconv⟩ := expanding_pointed_value_limit
    (fun m : ℕ => (m : ℝ)+1) (fun m => by positivity)
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    p r ε V hεlim u L A hA (by
      intro m
      filter_upwards [hdata m] with k hk
      exact ⟨hr k,hε k,hε1 k,hk.2.1.metric,hk.2.2.2.2.2.1,hk.2.2.2.2.2.2⟩)
  have hharm := hX.expanding_harmonic_limit hn (p∘a) (r∘a) (ε∘a) (V∘a)
    (fun k => hr (a k)) (fun k => hε (a k)) (fun k => hε1 (a k))
    (hεlim.comp ha.tendsto_atTop) (u∘a) (fun m k => w m (a k)) M hM (by
      intro m
      filter_upwards [ha.tendsto_atTop.eventually (hdata m)] with k hk
      exact ⟨hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1,hk.2.2.2.2.1⟩) f hfc hfL hconv
  exact ⟨a,f,ha,hfc,hharm,hfL,hconv⟩

end RegularPointCoordinates

end

end OAI
