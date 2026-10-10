import OAI.Geometry.RCD.Harmonic.HarmonicReplacementFamily
import OAI.Geometry.RCD.Sobolev.CompactRecoveryGlobalBounds
import OAI.Geometry.RCD.Sobolev.SharpWeightedTestRecovery
import OAI.Geometry.RCD.Sobolev.SmoothRecoveryGradientBound

namespace OAI

/-! # Actual harmonic candidates built from prescribed Euclidean tests

The recovered boundary values and harmonic replacements live in the
original Sobolev spaces. Both global L2 and rescaled energy bounds retain
the physical outer-ball normalization.
-/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.compact_test_harmonic_replacements {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) {S R : ℝ}
    (hS : 0<S) (hR : 0<R) (hRS : 2*R≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hcurvR : ∀ k, -1≤K*(2*(R*r k))^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    {ψ : Euclidean n → ℝ} (hψ : InteriorSmoothTest n S ψ) :
    ∃ C E : ℝ, 0<C ∧ 0≤E ∧ ∃ N : ℕ,
      ∃ u w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic,
        (∀ k, w k-u k∈SobolevSpace.dirichlet (hausdorff n X) hX.quadratic
            (ball (p (k+N)) (R*r (k+N))) ∧
          IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
            (ball (p (k+N)) (R*r (k+N))) (w k) ∧
          energyForm (hausdorff n X) hX.quadratic (w k) (w k)≤
            energyForm (hausdorff n X) hX.quadratic (u k) (u k) ∧
          ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k)‖^2≤
            C*(hausdorff n X).real (ball (p (k+N)) (S*r (k+N))) ∧
          r (k+N)^2*energyForm (hausdorff n X) hX.quadratic (w k) (w k)≤
            E*(hausdorff n X).real (ball (p (k+N)) (S*r (k+N))) ∧
          r (k+N)^2*energyForm (hausdorff n X) hX.quadratic (u k) (u k)≤
            E*(hausdorff n X).real (ball (p (k+N)) (S*r (k+N)))) ∧
        ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
          ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (k+N)) (S*r (k+N))),
            |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x-ψ (V (k+N) x)|≤δ := by
  obtain ⟨c,hc,hcS,N,u,huv,hug,huz,_⟩ :=
    hX.sharp_weighted_test_recovery hn hS p r ε V hr hcurv hε hε1 hεlim hV hψ
  obtain ⟨Q,_hQ,hub⟩ := compact_recovery_scaled_gradient_bound (hausdorff n X) hX.quadratic
    (hψ.1.of_le (by simp)) hψ.2.1 (fun k => p (k+N)) (fun k => r (k+N))
    (fun k => hr (k+N)) (fun k => V (k+N)) (fun k => (u k).val) huz (hug c hc.le hcS)
  obtain ⟨B,hB⟩ := hψ.2.1.exists_bound_of_continuous hψ.1.continuous
  let μ := hausdorff n X
  let : ∀ k, IsFiniteMeasure (μ.restrict (ball (p (k+N)) (S*r (k+N)))) := fun k => ⟨by
    simpa only [Measure.restrict_apply_univ] using hX.finiteOnBounded _ isBounded_ball⟩
  have hbounds := compact_recovery_global_bounds μ hX.quadratic hcS.le
    (fun k => p (k+N)) (fun k => r (k+N)) (fun k => (hr (k+N)).le)
    (fun k => (u k).val) (fun k x => ψ (V (k+N) x))
    (fun k x => by simpa only [Real.norm_eq_abs] using hB (V (k+N) x))
    (huv 1 zero_lt_one) huz hub
  obtain ⟨C,hC,M,w,hw⟩ := hX.harmonic_replacement_family hn hS hR hRS
    (sq_nonneg (B+1)) (sq_nonneg Q) (fun k => p (k+N)) (fun k => r (k+N))
    (fun k => ε (k+N)) (fun k => V (k+N)) (fun k => hr (k+N))
    (fun k => hcurvR (k+N)) (fun k => hV (k+N))
    (hεlim.comp (tendsto_add_atTop_nat N)) (fun k => (u k).val) hbounds
  refine ⟨C,Q^2,hC,sq_nonneg Q,M+N,(fun k => (u (k+M)).val),w,?_,?_⟩
  · intro k
    simpa only [Nat.add_assoc] using hw k
  · intro δ hδ
    simpa only [Nat.add_assoc] using (tendsto_add_atTop_nat M).eventually (huv δ hδ)

end RegularPointCoordinates

end

end OAI
