import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.GraphInverse
import OAI.Analysis.BiholderTransport.Regularity.MaximumConfiguration

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

structure MaximumRow (v : M → ℝ) (a D b bplus t : ℝ) (Bc Bo : ℝ → ℝ) (z : M) where
  q : subgradientGraph (n := n) (cTransform (modifiedDatum v a D b Bo))
  minimizing : q.1.2∈minimizingVectors q.1.1
  projection : graphProjection (cTransform (modifiedDatum v a D b Bo)) t q=z
  activeHull : q.1.2∈convexHull ℝ (activeLogs (modifiedDatum v a D b Bo) q.1.1)
  center : ∀ w,hopfLax (1-t) (modifiedDatum v a D b Bc) z=
    modifiedDatum v a D b Bc w+cost w z/(1-t) ↔ w=riemannianExp q.1.1 q.1.2
  value : regularizedComparison v a D bplus t Bc Bo (b,z)=
    modifiedExcess v a D b Bc Bo (riemannianExp q.1.1 q.1.2)-parameterPenalty bplus b
  parameter : ∀ (ι : Type) [Fintype ι] [Nonempty ι]
    (pj : ι → TangentSpace 𝓘(ℝ,Model n) q.1.1) (weights : ι → ℝ),
    (∀ i,0<weights i) → (∑ i,weights i=1) → (∑ i,weights i • pj i=q.1.2) →
    (∀ i,pj i∈activeLogs (modifiedDatum v a D b Bo) q.1.1) →
    1/4096+4*b/bplus ≤ Bc ((v (riemannianExp q.1.1 q.1.2)-a)/D)-
      ∑ i,weights i*Bo ((v (riemannianExp q.1.1 (pj i))-a)/D)

lemma WeakMTW.exists_maximum_row (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {a D b bplus t H : ℝ} {z : M}
    {Bc Bo : ℝ → ℝ} (hc : Continuous Bc) (ho : Continuous Bo)
    (hbound : ∀ s,0≤Bo s ∧ Bo s≤H) (ht : 0<t) (ht1 : t<1) (hb : 0≤b) (hbp : 0<bplus)
    (hdy : MDifferentiableAt 𝓘(ℝ,Model n) 𝓘(ℝ,ℝ)
      (hopfLax (1-t) (modifiedDatum v a D b Bc)) z)
    (hmax : ∀ᶠ q in 𝓝 (b,z),regularizedComparison v a D bplus t Bc Bo q≤
      regularizedComparison v a D bplus t Bc Bo (b,z)) :
    Nonempty (MaximumRow (n := n) v a D b bplus t Bc Bo z) := by
  obtain ⟨x,y,p,hact,hmin,hz,hy,hpole,hcenter,hvalue,hparameter⟩ :=
    hmtw.modified_maximum_configuration hv hc ho hbound ht ht1 hb hbp hdy hmax
  let q : subgradientGraph (n := n) (cTransform (modifiedDatum v a D b Bo)) :=
    ⟨⟨x,p⟩,active_hull_subset_normalSubdifferential (continuous_modifiedDatum hv a D b ho) x hact⟩
  refine ⟨⟨q,hmin,hz.symm,hact,?_,?_,?_⟩⟩
  · simpa only [hy] using hcenter
  · simpa only [hy] using hvalue
  · simpa only [hy] using hparameter

lemma MaximumRow.graph_inverse {v : M → ℝ} {a D b bplus t : ℝ} {Bc Bo : ℝ → ℝ} {z : M}
    (R : MaximumRow (n := n) v a D b bplus t Bc Bo z)
    (hmtw : WeakMTW (n := n) (M := M)) (hv : Continuous v) (ho : Continuous Bo)
    (ht : 0<t) (ht1 : t<1) :
    (hmtw.graphHomeomorph (continuous_modifiedDatum hv a D b ho) ht ht1).symm z=R.q := by
  apply (hmtw.graphHomeomorph (continuous_modifiedDatum hv a D b ho) ht ht1).injective
  exact (Homeomorph.apply_symm_apply _ _).trans R.projection.symm

end WeakMTWTransport

end

end OAI
