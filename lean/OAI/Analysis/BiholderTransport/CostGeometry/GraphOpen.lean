import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.BranchInverse
import OAI.Analysis.BiholderTransport.Contact.ActiveContinuationLocal
import OAI.Analysis.BiholderTransport.Contact.SubgradientUpper

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

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.local_projection_surjective (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈normalSubdifferential (n := n) (cTransform v) x)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (hID : ∀ q∈normalSubdifferential (n := n) (cTransform v) x, t • q∈injectivityDomain x) :
    ∀ O∈𝓝 (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M),
      ∀ᶠ y in 𝓝 (riemannianExp x (t • p)),
        ∃ z∈O, z.2∈normalSubdifferential (n := n) (cTransform v) z.1 ∧
          riemannianExp z.1 (t • z.2)=y := by
  intro O hO
  let y₀ := riemannianExp x (t • p)
  have htp := hID p hp
  obtain ⟨P,hP,hP0,_,hPinv⟩ := exists_smooth_exp_branch
    (⟨x,t • p⟩ : TangentBundle 𝓘(ℝ,Model n) M) (riemannianExp_interior_nonconjugate htp)
  let Q := fun q : M×M => tangentScale t⁻¹ (P q)
  have hQ : ContinuousAt Q (x,y₀) :=
    (contMDiff_tangentScale (E := Model n) (M := M)).continuous.continuousAt.comp
      (continuousAt_const.prodMk hP.continuousAt)
  have hQ0 : Q (x,y₀)=(⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M) := by
    dsimp only [Q,y₀]
    rw [hP0]
    simp only [tangentScale,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
  have hQO : ∀ᶠ q : M×M in 𝓝 (x,y₀), Q q∈O :=
    hQ.preimage_mem_nhds (hQ0.symm ▸ hO)
  have hPID : ∀ᶠ q : M×M in 𝓝 (x,y₀), (P q).2∈injectivityDomain (P q).1 := by
    have hmem : {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈injectivityDomain z.1} ∈
        𝓝 (P (x,y₀)) := by
      apply (isOpen_total_injectivityDomain (n := n) (M := M)).mem_nhds
      rw [hP0]
      exact htp
    exact hP.continuousAt.preimage_mem_nhds hmem
  have H := (hQO.and hPID).and hPinv
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp H
  have hpH : p∈convexHull ℝ (activeLogs (n := n) v x) :=
    normalSubdifferential_subset_active_hull hv x hp
  have hIDH : ∀ q∈convexHull ℝ (activeLogs (n := n) v x), t • q∈injectivityDomain x :=
    fun q hq => hID q (active_hull_subset_normalSubdifferential hv x hq)
  have hmin := hmtw.active_hull_nearby_local_min hv hpH ht ht1 hIDH U hU
  filter_upwards [hV,hmin] with y hy hh
  obtain ⟨a,ha,hmin⟩ := hh
  have hq := hUV (show (a,y)∈U ×ˢ V from ⟨ha,hy⟩)
  rcases hPa : P (a,y) with ⟨b,r⟩
  change (tangentScale t⁻¹ (P (a,y))∈O ∧
    (P (a,y)).2∈injectivityDomain (P (a,y)).1) ∧
    (P (a,y)).1=a ∧ riemannianExp (P (a,y)).1 (P (a,y)).2=y at hq
  rw [hPa] at hq
  have hb : b=a := hq.2.1
  subst b
  have hr : r∈injectivityDomain a := hq.1.2
  have hE : riemannianExp a r=y := hq.2.2
  have htr : t • (t⁻¹ • r)=r := by rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  refine ⟨⟨a,t⁻¹ • r⟩,?_,?_,?_⟩
  · exact hq.1.1
  · apply local_min_divided_cost_subgradient ht.ne'
    · simpa only [htr] using hr
    · simpa only [htr,hE] using hmin
  · simpa only [htr] using hE

end WeakMTWTransport

end

end OAI
