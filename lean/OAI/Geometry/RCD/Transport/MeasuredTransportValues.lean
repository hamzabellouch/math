import OAI.Geometry.RCD.Transport.MeasuredTransportData
import OAI.Geometry.RCD.Metric.PointedMeasureValues

namespace OAI

/-! # The endpoint means of actual Sobolev functions have the prescribed value limits -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem MeasuredTransportData.mean_difference_tendsto {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} {p : ℕ → X} {r ε : ℕ → ℝ} {S τ B : ℝ}
    {v : ℕ → X → Euclidean n} {α β : ProbabilityMeasure (Euclidean n)} {c₀ : ℝ}
    (D : MeasuredTransportData hX p r S τ v α β c₀)
    (hS : 0<S) (hτ : 0≤τ) (hτB : τ<B) (hBS : B≤S)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    {g : Euclidean n → ℝ} {L : ℝ≥0} (hg : LipschitzOnWith L g (closedBall 0 B))
    (hclose : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
      dist x (p (k+D.offset))≤τ*r (k+D.offset) →
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (v (k+D.offset) x)|≤δ) :
    Tendsto (fun k =>
      (∫ γ : C(Time,X), SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) (γ 1)
        ∂(D.plan k : Measure C(Time,X)))-
      (∫ γ : C(Time,X), SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) (γ 0)
        ∂(D.plan k : Measure C(Time,X)))) atTop
      (𝓝 ((∫ z, g z ∂(β : Measure (Euclidean n)))-(∫ z, g z ∂(α : Measure (Euclidean n))))) := by
  let μ := hausdorff n X
  let C := fun k => ENNReal.ofReal (D.control k)*(μ (ball (p (k+D.offset)) (S*r (k+D.offset))))⁻¹
  have hC (k : ℕ) : C k≠⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr (hX.fullSupport _ _ (mul_pos hS (hr _))).ne')
  have hmean (σ : ℕ → ProbabilityMeasure X)
      (hb : ∀ k, (σ k : Measure X)≤C k • μ)
      (hs : ∀ k, ∀ᵐ x ∂(σ k : Measure X), dist x (p (k+D.offset))≤τ*r (k+D.offset))
      {ν : ProbabilityMeasure (Euclidean n)}
      (hw : Tendsto (fun k => (σ k).map (v (k+D.offset))) atTop (𝓝 ν)) :
      Tendsto (fun k => ∫ x, SobolevSpace.toLp μ hX.quadratic (w k) x ∂(σ k : Measure X))
        atTop (𝓝 (∫ z, g z ∂(ν : Measure (Euclidean n)))) := by
    refine pointed_local_value_integrals hτ (hτB.le.trans hBS) hτB
      (fun k => p (k+D.offset)) (fun k => r (k+D.offset)) (fun k => ε (k+D.offset))
      (fun k => v (k+D.offset)) (fun k => hr (k+D.offset))
      (hεlim.comp (tendsto_add_atTop_nat D.offset)) (fun k => (hv (k+D.offset)).metric)
      (fun k => (hv (k+D.offset)).measurable) σ hs hw (fun k => SobolevSpace.toLp μ hX.quadratic (w k)) ?_ hg ?_
    · intro k
      exact ((Lp.memLp _).of_measure_le_smul (hC k) (hb k)).integrable (by norm_num)
    · intro δ hδ
      filter_upwards [hclose δ hδ] with k hk
      have he := (Measure.absolutelyContinuous_of_le_smul (hb k)).ae_le hk
      filter_upwards [he,hs k] with x hx hsx
      exact hx hsx
  have hl := hmean D.left D.left_bound D.left_support D.left_limit
  have hr' := hmean D.right D.right_bound D.right_support D.right_limit
  have hend (k : ℕ) := optimalPlan_endpoints (D.left k : Measure X) (D.right k : Measure X)
    (D.plan k : Measure C(Time,X)) (D.optimal k)
  have he0 (k : ℕ) : (∫ γ : C(Time,X), SobolevSpace.toLp μ hX.quadratic (w k) (γ 0)
      ∂(D.plan k : Measure C(Time,X)))=∫ x, SobolevSpace.toLp μ hX.quadratic (w k) x ∂(D.left k : Measure X) := by
    rw [← integral_map (measurable_path_eval 0).aemeasurable
      (Lp.stronglyMeasurable _).aestronglyMeasurable,(hend k).1]
  have he1 (k : ℕ) : (∫ γ : C(Time,X), SobolevSpace.toLp μ hX.quadratic (w k) (γ 1)
      ∂(D.plan k : Measure C(Time,X)))=∫ x, SobolevSpace.toLp μ hX.quadratic (w k) x ∂(D.right k : Measure X) := by
    rw [← integral_map (measurable_path_eval 1).aemeasurable
      (Lp.stronglyMeasurable _).aestronglyMeasurable,(hend k).2]
  simpa only [he0,he1,μ] using hr'.sub hl

end RegularPointCoordinates

end

end OAI
