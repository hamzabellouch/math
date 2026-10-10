import Mathlib
import OAI.Analysis.BiholderTransport.Contact.GlobalSupport
import OAI.Analysis.BiholderTransport.Regularity.EuclideanUpper

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.subgradient_dual_contact (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈normalSubdifferential (n := n) u x) :
    p∈minimizingVectors x ∧ contactGap u v x (riemannianExp x p)=0 := by
  have hs := hmtw.global_support hv (show p∈normalSubdifferential (cTransform v) x by rwa [←hdual.1])
  rw [←hdual.1] at hs
  refine ⟨hs.1,le_antisymm ?_ (dualPair_gap_nonneg hv hdual _ _)⟩
  have hc : v (riemannianExp x p) ≤ -u x-cost x (riemannianExp x p) := by
    rw [hdual.2]
    apply (cTransform_le_iff hu _ _).mpr
    intro a
    have H := hs.2 a
    rw [cost_symm (riemannianExp x p) a]
    linarith
  dsimp [contactGap]
  linarith

lemma WeakMTW.dual_hopfLax_identity (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hdual : IsCostDualPair u v) {t : ℝ} (ht : 0<t) (ht1 : t<1) :
    hopfLax t u = fun z => -hopfLax (1-t) v z := by
  funext z
  obtain ⟨q,hq⟩ := surjective_graphProjection (n := n) hu ht z
  have hc := hmtw.subgradient_dual_contact hu hv hdual q.2
  let y := riemannianExp q.1.1 q.1.2
  have hsplit := splitNormalAction_contact hc.1 ht ht1
  change cost (riemannianExp q.1.1 0) (graphProjection u t q)/t+
    cost (graphProjection u t q) y/(1-t) = cost (riemannianExp q.1.1 0) y at hsplit
  rw [riemannianExp_zero,hq] at hsplit
  have hleft := hopfLax_le hu t z q.1.1
  have hright := hopfLax_le hv (1-t) z y
  rw [cost_symm y z] at hright
  have hcontact : u q.1.1+cost q.1.1 y+v y=0 := hc.2
  have hnonneg := dual_hopfLax_sum_nonneg hu hv hdual ht ht1 z
  linarith

lemma WeakMTW.hopfLax_graph_value (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (q : subgradientGraph (n := n) (cTransform v)) :
    hopfLax t (cTransform v) (graphProjection (cTransform v) t q) =
      cTransform v q.1.1+cost q.1.1 (graphProjection (cTransform v) t q)/t :=
  hopfLax_eq_of_min (continuous_cTransform hv) t _ _
    (global_min_of_injective_graphProjection (continuous_cTransform hv) ht
      (hmtw.injective_graphProjection hv ht ht1) q).2

end WeakMTWTransport

end

end OAI
