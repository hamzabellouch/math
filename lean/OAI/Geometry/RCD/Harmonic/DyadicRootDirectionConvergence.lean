import OAI.Geometry.RCD.Harmonic.DyadicRootLinearLimit
import OAI.Geometry.RCD.Sobolev.EverySubsequenceEventual

namespace OAI

/-! # Sharp estimates for the full sequence of root-normalized directions -/

open Set Metric Filter MeasureTheory
open scoped Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem dyadic_root_unit_direction_convergence {K : ℝ} (m : ℕ) (hm : 2 ≤ m+1)
    (hX : NoncollapsedRCD K (m+1) X) [(hausdorff (m+1) X).Regular]
    {a κ : ℝ} (ha : 0 ≤ a)
    (hBG : BallVolumeComparison (hausdorff (m+1) X) (comparisonModelVolume m a))
    (hκ : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hsmall : ((m+1 : ℕ) : ℝ)^2*(normalizationVolumeRatio m*κ) ≤ 1/2)
    (p : ℕ → X) (r ε : ℕ → ℝ) (d : ℕ → ℕ)
    (hr : ∀ k, 0 < r k) (hd : Tendsto d atTop atTop)
    (hcurv : ∀ k, -1 ≤ K*(r k)^2)
    (hcurv5 : ∀ k, -1 ≤ K*(5*r k)^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0))
    (V : ℕ → X → Euclidean (m+1))
    (hV : ∀ j : ℕ, ∀ᶠ k in atTop, IsMeasuredEuclideanApproximation (hausdorff (m+1) X)
      (m+1) (p k) (r k) ((j : ℝ)+1) (ε k) (V k))
    (u : ℕ → Fin (m+1) → SobolevSpace (hausdorff (m+1) X) hX.quadratic)
    (v : ℕ → X → Euclidean (m+1)) (A : ℕ → Euclidean (m+1) ≃L[ℝ] Euclidean (m+1))
    (hA : ∀ k, IsExactMeanNormalization (hausdorff (m+1) X) hX.quadratic
      (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u k))
      (ball (p k) (r k)) measurableSet_ball (A k))
    (hscale : ∀ k j, j ≤ d k → a*(3*((2 : ℝ)^j*r k)) ≤ 1)
    (hframes : ∀ k j, j ≤ d k → ∃ (S : Euclidean (m+1) ≃L[ℝ] Euclidean (m+1))
      (w : X → Euclidean (m+1)),
      FirstOrderSplittingOn (hausdorff (m+1) X) hX.quadratic (p k) ((2 : ℝ)^j*r k) κ
        (transformedColumn (hausdorff (m+1) X) hX.quadratic (u k) S) w ∧
      IsExactMeanNormalization (hausdorff (m+1) X) hX.quadratic
        (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u k))
        (ball (p k) ((2 : ℝ)^j*r k)) measurableSet_ball S)
    (hv : ∀ k, ContinuousOn (v k) (ball (p k) ((2 : ℝ)^(d k)*r k)))
    (hrep : ∀ k i, SobolevSpace.toLp (hausdorff (m+1) X) hX.quadratic (u k i) =ᵐ[
      (hausdorff (m+1) X).restrict (ball (p k) ((2 : ℝ)^(d k)*r k))] fun x => v k x i)
    (hu : ∀ k i, IsSobolevHarmonicOn (hausdorff (m+1) X) hX.quadratic
      (ball (p k) ((2 : ℝ)^(d k)*r k)) (u k i)) (z : Euclidean (m+1)) (hz : ‖z‖ = 1) :
    (∀ β : ℝ, 0 < β → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff (m+1) X).restrict (ball (p k) (3*r k)),
        localGamma (hausdorff (m+1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u k) (A k z))
          (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u k) (A k z)) x ≤ 1+β) ∧
    Tendsto (fun k => ((hausdorff (m+1) X).real (ball (p k) (2*r k)))⁻¹*
      ∫ x in ball (p k) (2*r k),
        |localGamma (hausdorff (m+1) X) hX.quadratic
          (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u k) (A k z))
          (sobolevColumnMap (hausdorff (m+1) X) hX.quadratic (u k) (A k z)) x-1|
        ∂hausdorff (m+1) X) atTop (𝓝 0) := by
  let μ := hausdorff (m+1) X
  let G := fun k => sobolevColumnMap μ hX.quadratic (u k) (A k z)
  let E := fun k => (μ.real (ball (p k) (2*r k)))⁻¹*
    ∫ x in ball (p k) (2*r k), |localGamma μ hX.quadratic (G k) (G k) x-1| ∂μ
  have hex (α : ℕ → ℕ) (hα : Tendsto α atTop atTop) : ∃ b : ℕ → ℕ,
      (∀ β : ℝ, 0 < β → ∀ᶠ k in atTop,
        ∀ᵐ x ∂μ.restrict (ball (p (α (b k))) (3*r (α (b k)))),
          localGamma μ hX.quadratic (G (α (b k))) (G (α (b k))) x ≤ 1+β) ∧
      Tendsto (fun k => E (α (b k))) atTop (𝓝 0) := by
    obtain ⟨b,_,_,_,_,hs,he⟩ := dyadic_root_unit_linear_limit m hm hX ha hBG hκ hκ1 hsmall
      (p∘α) (r∘α) (ε∘α) (d∘α) (fun k => hr (α k)) (hd.comp hα)
      (fun k => hcurv (α k)) (fun k => hcurv5 (α k))
      (fun k => hε (α k)) (fun k => hε1 (α k)) (hεlim.comp hα) (V∘α)
      (fun j => hα.eventually (hV j)) (u∘α) (v∘α) (A∘α)
      (fun k => hA (α k)) (fun k => hscale (α k)) (fun k => hframes (α k))
      (fun k => hv (α k)) (fun k => hrep (α k)) (fun k => hu (α k)) z hz
    exact ⟨b,hs,he⟩
  constructor
  · intro β hβ
    apply eventually_of_every_subsequence
    intro α hα
    obtain ⟨b,hs,_⟩ := hex α hα.tendsto_atTop
    exact ⟨b,hs β hβ⟩
  · apply tendsto_of_subseq_tendsto
    intro α hα
    obtain ⟨b,_,he⟩ := hex α hα
    exact ⟨b,he⟩

end RegularPointCoordinates

end

end OAI
