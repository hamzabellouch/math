import OAI.Geometry.RCD.Sobolev.CompactBoundaryLayerSequence
import OAI.Geometry.RCD.Coordinates.AnnularSquareLimit

namespace OAI

/-! # The actual boundary-layer bound survives in the Euclidean limit -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem CompactHarmonicBoundaryLimit.truncated_layer_bound {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hn : 2≤n)
    {p : ℕ → X} {r ε : ℕ → ℝ} {V : ℕ → X → Euclidean n} {S R : ℝ} {ψ : Euclidean n → ℝ}
    (d : CompactHarmonicBoundaryLimit hX p r V S R ψ)
    (hS : 0<S) (_hR : 0<R) (hRS : R≤S)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*(S*r k)^2)
    (hε : ∀ k, 0≤ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    {M : ℝ≥0} (hψ : LipschitzWith M ψ) :
    ∃ A : ℝ, 0<A ∧ ∀ δ : ℝ, 0<δ → 4*δ≤R → R+2*δ≤S →
      ∀ b : ℝ, R-δ<b → b<R →
        (volume.real (ball (0:Euclidean n) S))⁻¹*
          (∫ z in ball 0 b \ ball 0 (R-δ), (d.value z-ψ z)^2)≤A*δ^2 := by
  obtain ⟨A,hA,hbound⟩ := d.boundary_layer hn hr hcurv hε hεlim hV
  refine ⟨A,hA,?_⟩
  intro δ hδ hδR hδS b hab hbR
  let t := (b+R)/2
  have hbt : b<t := by dsimp only [t]; linarith
  have htR : t<R := by dsimp only [t]; linarith
  have ha : 0<R-δ := by linarith
  obtain ⟨L,hL⟩ := d.localLipschitz t htR
  let a := fun k => d.subsequence k+d.shift
  have hta : Tendsto a atTop atTop := (tendsto_add_atTop_nat d.shift).comp d.strictMono.tendsto_atTop
  have hlim := hX.outer_normalized_annular_square_limit hS ha hab hbt (htR.le.trans hRS)
    (p∘a) (r∘a) (ε∘a) (V∘a) (fun k => hr (a k)) (fun k => hV (a k)) (hεlim.comp hta)
    (fun k => d.target (d.subsequence k)-d.boundary (d.subsequence k))
    (fun z => d.value z-ψ z) (hL.sub hψ.lipschitzOnWith)
    (d.difference_converges hr hRS b (ha.trans hab) hbR)
  apply le_of_tendsto hlim
  filter_upwards [hbound δ hδ hδR hδS] with k hk
  have hsub : ball (p (a k)) (b*r (a k)) \ ball (p (a k)) ((R-δ)*r (a k))⊆
      closedBall (p (a k)) (R*r (a k)) \ ball (p (a k)) ((R-δ)*r (a k)) := by
    intro x hx
    exact ⟨ball_subset_closedBall ((ball_subset_ball
      (mul_le_mul_of_nonneg_right hbR.le (hr _).le)) hx.1),hx.2⟩
  have hm := setIntegral_mono_set
    (Lp.memLp (SobolevSpace.toLp (hausdorff n X) hX.quadratic
      (d.target (d.subsequence k)-d.boundary (d.subsequence k)))).integrable_sq.restrict
    (Filter.Eventually.of_forall fun x => sq_nonneg _) (Filter.Eventually.of_forall hsub)
  exact (mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr measureReal_nonneg)).trans hk

end RegularPointCoordinates

end

end OAI
