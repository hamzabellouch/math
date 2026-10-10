import OAI.Geometry.RCD.Transport.FirstOrderDistanceDistortion

namespace OAI

/-! # Uniform distortion of the original coordinates on inner physical balls -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_uniform_distortion {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (p : ℕ → X) (r ε : ℕ → ℝ) (hr : ∀ k, 0<r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hε0 : Tendsto ε atTop (𝓝 0))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (16*r k) (ε k) (u k) (v k))
    {τ : ℝ} (hτ : 0<τ) :
    ∀ᶠ k in atTop, ∀ x y, dist x (p k)≤r k/48 → dist y (p k)≤r k/48 →
      |dist (v k x) (v k y)/r k-dist x y/r k|≤τ := by
  classical
  by_contra hnot
  obtain ⟨a,ha,hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp hnot)
  have hex (k : ℕ) : ∃ x y, dist x (p (a k))≤r (a k)/48 ∧
      dist y (p (a k))≤r (a k)/48 ∧
      τ < |dist (v (a k) x) (v (a k) y)/r (a k)-dist x y/r (a k)| := by
    simpa only [not_forall,not_le,exists_prop] using hbad k
  choose x y hx hy hfail using hex
  have hlim := hX.first_order_distance_distortion hn hK (p∘a) x y (r∘a) (ε∘a)
    (fun k => hr (a k)) (hr0.comp ha.tendsto_atTop) (fun k => hcurv (a k))
    (fun k => hε (a k)) (fun k => hε1 (a k)) (hε0.comp ha.tendsto_atTop)
    (u∘a) (v∘a) (fun k => hsplit (a k)) hx hy
  obtain ⟨k,hk⟩ := (hlim.eventually (gt_mem_nhds hτ)).exists
  exact (not_lt_of_ge hk.le) (hfail k)

end RegularPointCoordinates

end

end OAI
