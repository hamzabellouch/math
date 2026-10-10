import OAI.Geometry.RCD.Harmonic.FiniteGramIsometricLimit
import OAI.Geometry.RCD.Harmonic.PointedAffineLimitApproximation
import OAI.Geometry.RCD.Sobolev.EverySubsequenceEventual

namespace OAI

/-! # The actual harmonic frame approximates a Euclidean ball -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_frame_approximation {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1 ≤ K*r k^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (ε k) (V k))
    (w : Fin n → ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ i k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w i k))
    {M : ℝ} (hM : 0 < M) (hnorm : ∀ i k, harmonicTargetNorm hX (p k) (5*r k) (w i k) ≤ M)
    (hv : ∀ k, ContinuousOn (v k) (ball (p k) (5*r k))) (hzero : ∀ k, v k (p k)=0)
    (hrep : ∀ i k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i k) =ᵐ[
      (hausdorff n X).restrict (ball (p k) (5*r k))] fun x => v k x i)
    (hgram : ∀ i j, Tendsto (fun k => ((hausdorff n X).real (ball (p k) (5*r k)))⁻¹*
      ∫ x in ball (p k) (4*r k),
        |r k^2*localGamma (hausdorff n X) hX.quadratic (w i k) (w j k) x-
          (if i=j then 1 else 0)| ∂hausdorff n X) atTop (𝓝 0)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop,
      IsPointedApproximation (p k) 0 (r k) (5/2) τ (v k) := by
  let := hX.openPos K n
  intro τ hτ
  apply eventually_of_every_subsequence
  intro α hα
  obtain ⟨β,hβ,g,T,haff,hconv⟩ := hX.finite_harmonic_isometric_limit hn
    (p∘α) (r∘α) (ε∘α) (V∘α) (fun k => hr (α k)) (fun k => hcurv (α k))
    (fun k => hε (α k)) (fun k => hε1 (α k)) (hεlim.comp hα.tendsto_atTop)
    (fun k => hV (α k)) (fun i => w i∘α) (fun i k => hw i (α k)) hM
    (fun i k => hnorm i (α k)) (fun i j => (hgram i j).comp hα.tendsto_atTop)
  refine ⟨β,?_⟩
  exact pointed_affine_limit_approximation (hausdorff n X) hX.quadratic
    (p∘α∘β) (r∘α∘β) (ε∘α∘β) (V∘α∘β) (v∘α∘β)
    (fun k => hr (α (β k))) (fun k => hε (α (β k)))
    ((hεlim.comp hα.tendsto_atTop).comp hβ.tendsto_atTop)
    (fun k => (hV (α (β k))).metric) (fun i => w i∘α∘β)
    (fun k => hv (α (β k))) (fun k => hzero (α (β k)))
    (fun i k => hrep i (α (β k))) g T haff hconv τ hτ

end RegularPointCoordinates

end

end OAI
