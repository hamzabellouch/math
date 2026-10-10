import OAI.Geometry.RCD.Harmonic.FirstOrderSubsequenceApproximation

namespace OAI

/-! # Uniform small-scale Euclidean approximation by the original coordinates -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_small_scale_approximation {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    {τ : ℝ} (hτ : 0<τ) :
    ∃ s₀ ε : ℝ, 0<s₀ ∧ 0<ε ∧ ∀ (p : X) (s : ℝ), 0<s → s ≤ s₀ →
      -1≤K*(81920*s)^2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (81920*s) ε u v →
        IsPointedApproximation p 0 s 2 τ (fun x => s⁻¹ • (v x-v p)) := by
  classical
  by_contra hnot
  push Not at hnot
  let e : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
  have he (k : ℕ) : 0<e k := by dsimp [e]; positivity
  have he1 (k : ℕ) : e k≤1 := by
    dsimp [e]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose p s hs hs0 hcurv u v hsplit hbad using (fun k => hnot (e k) (e k) (he k) (he k))
  let r : ℕ → ℝ := fun k => 1024*s k
  have hr (k : ℕ) : 0<r k := mul_pos (by norm_num) (hs k)
  have hr0 : Tendsto r atTop (𝓝 0) := by
    apply squeeze_zero (fun k => (hr k).le) (fun k => ?_) (by
      simpa only [mul_zero] using he0.const_mul 1024)
    exact mul_le_mul_of_nonneg_left (hs0 k) (by norm_num)
  have hc (k : ℕ) : -1≤K*(80*r k)^2 := by
    simpa only [show 80*r k=81920*s k by dsimp [r]; ring] using hcurv k
  have hsp (k : ℕ) : FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (80*r k) (e k) (u k) (v k) := by
    simpa only [show 80*r k=81920*s k by dsimp [r]; ring] using hsplit k
  obtain ⟨a,_ha,ha⟩ := hX.first_order_subsequence_approximation hn hK p r e hr hr0 hc
    (fun k => (he k).le) he1 he0 u v hsp hτ
  obtain ⟨k,hk⟩ := ha.exists
  apply hbad (a k)
  simpa only [show r (a k)/1024=s (a k) by dsimp [r]; ring] using hk

end RegularPointCoordinates

end

end OAI
