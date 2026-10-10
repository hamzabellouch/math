import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.GraphFilter
import OAI.Geometry.WeakHessian.LocalBounds.TripleTimeContinuity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile188
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]

lemma continuousOn_graph_weakGradient (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A : Y → Lp ℝ 2 m}
    (hg : ∀ s,IsLaplacian m (u s : X → ℝ) (A s)) {S : Set Y}
    (hu : ContinuousOn u S) (hA : ContinuousOn A S) :
    ContinuousOn (fun s => (hg s).1.2.2.toLp (weakGradient m (u s : X → ℝ))) S := by
  intro s hs
  apply filter_graph_tendsto_weakGradient hfin hpar hg (hg s)
  · simpa only [Lp.toLp_coeFn] using (hu s hs).tendsto
  · simpa only [Lp.toLp_coeFn] using (hA s hs).tendsto

lemma continuousOn_graph_gamma_pairing (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {u A ξ : Y → Lp ℝ 2 m}
    (hg : ∀ s,IsLaplacian m (u s : X → ℝ) (A s)) {S : Set Y}
    (hu : ContinuousOn u S) (hA : ContinuousOn A S) (hξ : ContinuousOn ξ S)
    (n : ℕ) (hD : ∀ s ∈ S,∀ᵐ x ∂m,|weakGradient m (u s : X → ℝ) x| ≤ (n:ℝ))
    {k : X → ℝ} (hkm : AEStronglyMeasurable k m) {B : ℝ} (hkb : ∀ᵐ x ∂m,|k x| ≤ B) :
    ContinuousOn (fun s => ∫ x,(ξ s x*k x)*gamma m (u s : X → ℝ) (u s) x ∂m) S := by
  let D := fun s => (hg s).1.2.2.toLp (weakGradient m (u s : X → ℝ))
  let M := boundedMulLp hkm hkb
  have hcD : ContinuousOn D S := continuousOn_graph_weakGradient hfin hpar hg hu hA
  have hDb : ∀ s ∈ S,∀ᵐ x ∂m,|D s x| ≤ (n:ℝ) := by
    intro s hs
    filter_upwards [(hg s).1.2.2.coeFn_toLp,hD s hs] with x hx hb
    simpa only [D,hx] using hb
  have hc := continuousOn_integral_square_mul hcD (M.continuous.comp_continuousOn hξ) n hDb
  apply hc.congr
  intro s hs
  apply integral_congr_ae
  filter_upwards [(hg s).1.2.2.coeFn_toLp,boundedMulLp_ae hkm hkb (ξ s),
    gamma_self (m := m) (u s : X → ℝ)] with x hx hy hΓ
  dsimp only [D,Function.comp_def,M]
  rw [hx,hy,hΓ]
  ring
end WeakHessian

end
end InlinedFile188

end OAI
