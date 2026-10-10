import Mathlib
import OAI.Analysis.BiholderTransport.LocalFlow.SmoothFlowEndpoint
import OAI.Analysis.BiholderTransport.Calculus.SmoothExtensionNear

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [HasContDiffBump E]

lemma exists_smooth_local_flow_on {f : E → E} {S : Set E}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S) {a : E} (ha : a ∈ S) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ S ∧ ∃ Φ : (ℝ × E) → E,
      ContDiffOn ℝ ∞ Φ (Ioo (-r) r ×ˢ Metric.ball a r) ∧
      (∀ x ∈ Metric.ball a r, Φ (0,x) = x) ∧
      ∀ t ∈ Ioo (-r) r, ∀ x ∈ Metric.ball a r,
        Φ (t,x) ∈ S ∧ HasDerivAt (fun s => Φ (s,x)) (f (Φ (t,x))) t := by
  obtain ⟨g,hg,hgf⟩ := exists_smooth_extension_near hS hf ha
  obtain ⟨r,hr,Φ,hΦ,hΦ0,hΦder⟩ := exists_smooth_local_flow g hg a
  have hcenter : ((0:ℝ),a) ∈ Ioo (-r) r ×ˢ Metric.ball a r :=
    ⟨⟨neg_neg_of_pos hr,hr⟩,Metric.mem_ball_self hr⟩
  have hcont : ContinuousAt Φ (0,a) :=
    (hΦ.contDiffAt ((isOpen_Ioo.prod Metric.isOpen_ball).mem_nhds hcenter)).continuousAt
  have hΦa : Φ (0,a) = a := hΦ0 a (Metric.mem_ball_self hr)
  have hnear : ∀ᶠ z in 𝓝 ((0:ℝ),a), Φ z ∈ S ∧ g (Φ z) = f (Φ z) := by
    have h := hcont.eventually (show ∀ᶠ y in 𝓝 (Φ (0,a)), y ∈ S ∧ g y = f y from by
      rw [hΦa]
      exact (show ∀ᶠ y in 𝓝 a, y ∈ S from hS.mem_nhds ha).and hgf)
    exact h
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min (r/2) (ε/2)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
  have hδε : δ < ε := (min_le_right _ _).trans_lt (by linarith)
  have hdom : Ioo (-δ) δ ×ˢ Metric.ball a δ ⊆ Ioo (-r) r ×ˢ Metric.ball a r := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1],hz.1.2.trans hδr⟩,lt_trans hz.2 hδr⟩
  have himg : ∀ t ∈ Ioo (-δ) δ, ∀ x ∈ Metric.ball a δ,
      Φ (t,x) ∈ S ∧ g (Φ (t,x)) = f (Φ (t,x)) := by
    intro t ht x hx
    apply hεsub
    change dist (t,x) (0,a) < ε
    rw [Prod.dist_eq,max_lt_iff,Real.dist_eq,sub_zero]
    exact ⟨(abs_lt.mpr ht).trans hδε,lt_trans hx hδε⟩
  refine ⟨δ,hδ,?_,Φ,hΦ.mono hdom,?_,?_⟩
  · intro x hx
    have h0 : Φ (0,x) = x := hΦ0 x (lt_trans hx hδr)
    exact h0 ▸ (himg 0 ⟨neg_neg_of_pos hδ,hδ⟩ x hx).1
  · intro x hx
    exact hΦ0 x (lt_trans hx hδr)
  · intro t ht x hx
    refine ⟨(himg t ht x hx).1,?_⟩
    rw [←(himg t ht x hx).2]
    have hz := hdom (show (t,x) ∈ Ioo (-δ) δ ×ˢ Metric.ball a δ from ⟨ht,hx⟩)
    exact hΦder t hz.1 x hz.2

end WeakMTWTransport

end

end OAI
