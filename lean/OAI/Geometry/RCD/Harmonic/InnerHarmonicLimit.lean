import OAI.Geometry.RCD.Metric.InnerMeasuredSubsequence
import OAI.Geometry.RCD.Harmonic.InnerHarmonicNormBound
import OAI.Geometry.RCD.Harmonic.BoundedHarmonicCompactness

namespace OAI

/-! # A classical limit for the actual inner-ball harmonic candidates

Both the measured maps and the normalizing bound on the smaller ball are
derived from the original outer approximation and global L2 bound.
-/

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.inner_harmonic_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {S R C : ℝ} (hS : 0<S) (hR : 0<R) (hRS : R≤S) (hC : 0<C)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (R*r k)) (w k))
    (hbound : ∀ k, ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k)‖^2≤
      C*(hausdorff n X).real (ball (p k) (S*r k))) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∃ g : Euclidean n → ℝ,
      Measurable g ∧ ContinuousOn g (ball 0 R) ∧ EuclideanWeakHarmonicOn g R ∧
      ContDiffOn ℝ ∞ g (ball 0 R) ∧
      (∀ W<R, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W)) ∧
      ∀ W : ℝ, 0<W → W<R → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (a k)) (W*r (a k))),
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w (a k)) x-g (V (a k) x)|≤δ := by
  let η : ℕ → ℝ := fun k => 1/((k+1:ℕ):ℝ)
  have hη (k : ℕ) : 0<η k := by dsimp only [η]; positivity
  have hη1 (k : ℕ) : η k≤1 := by
    apply (div_le_one (by positivity : (0:ℝ)<((k+1:ℕ):ℝ))).mpr
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hηlim : Tendsto η atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  obtain ⟨a,ha,hVa⟩ := inner_measured_subsequence hS hR hRS hr hε hV
    (fun k => (hX.finiteOnBounded _ isBounded_ball).ne)
    (fun k => ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne) hεlim hη
  obtain ⟨M,hM,hMb⟩ := hX.inner_harmonic_norm_bound hS hR hRS hC p r ε V hr hV hεlim w hbound
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ha.tendsto_atTop.eventually hMb)
  let b : ℕ → ℕ := fun k => a (k+N)
  have hb : StrictMono b := ha.comp (fun _ _ h => Nat.add_lt_add_right h N)
  obtain ⟨c,hc,g,hgm,hgc,hgw,hgs,hgL,hconv⟩ := hX.bounded_harmonic_compactness hn hR hM
    (p∘b) (r∘b) (fun k => η (k+N)) (V∘b)
    (fun k => hr (b k)) (fun k => hcurv (b k)) (fun k => (hη (k+N)).le)
    (fun k => hη1 (k+N)) (hηlim.comp (tendsto_add_atTop_nat N))
    (fun k => hVa (k+N)) (w∘b) (fun k => hw (b k))
    (fun k => hN (k+N) (Nat.le_add_left N k))
  exact ⟨b∘c,hb.comp hc,g,hgm,hgc,hgw,hgs,hgL,hconv⟩

end RegularPointCoordinates

end

end OAI
