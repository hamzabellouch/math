import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.NormalSubdifferential
import OAI.Analysis.BiholderTransport.Coordinates.MetricLocalGrowth
import OAI.Analysis.BiholderTransport.Regularity.LocalMinStrictGrowth

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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

omit [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma smooth_lower_support_mem_normalSubdifferential {u : M → ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {g : TangentSpace 𝓘(ℝ,Model n) x → ℝ}
    (hg : HasFDerivAt g (innerSL ℝ p) 0)
    (hs : ∀ᶠ h in 𝓝 0, g h-g 0≤u (riemannianExp x h)-u x) :
    p ∈ normalSubdifferential (n := n) u x := by
  intro ε hε
  filter_upwards [hasFDerivAt_affine_lower_support hg ε hε,hs] with h hh hk
  exact hh.trans hk

lemma local_min_divided_cost_subgradient {u : M → ℝ} {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ} (ht : t≠0)
    (hID : t • p ∈ injectivityDomain x)
    (hmin : IsLocalMin (fun z => u z+cost z (riemannianExp x (t • p))/t) x) :
    p ∈ normalSubdifferential (n := n) u x := by
  let g := fun h : TangentSpace 𝓘(ℝ,Model n) x => (-t⁻¹)*normalCost x (t • p) h
  have hg : HasFDerivAt g (innerSL ℝ p) 0 := by
    apply ((normalCost_hasFDerivAt_zero hID).const_smul (-t⁻¹)).congr_fderiv
    ext h
    simp only [smul_apply,innerSL_apply_apply,inner_neg_left,real_inner_smul_left,smul_eq_mul]
    field_simp
  apply smooth_lower_support_mem_normalSubdifferential hg
  have hm : ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0,
      u x+cost x (riemannianExp x (t • p))/t≤
        u (riemannianExp x h)+cost (riemannianExp x h) (riemannianExp x (t • p))/t := by
    have hc := (continuous_riemannianExp (n := n) x).continuousAt (x := 0) |>.tendsto
    rw [riemannianExp_zero] at hc
    exact hc.eventually hmin
  filter_upwards [hm] with h hh
  dsimp only [g,normalCost]
  rw [riemannianExp_zero]
  simp only [div_eq_mul_inv] at hh
  nlinarith

lemma WeakMTW.active_hull_nearby_local_min (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ convexHull ℝ (activeLogs (n := n) v x))
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (hID : ∀ q ∈ convexHull ℝ (activeLogs (n := n) v x), t • q ∈ injectivityDomain x) :
    ∀ O ∈ 𝓝 x, ∀ᶠ y in 𝓝 (riemannianExp x (t • p)),
      ∃ z∈O, IsLocalMin (fun w => cTransform v w+cost w y/t) z := by
  let : Nonempty M := ⟨x⟩
  apply exists_local_min_of_strict_growth
  · exact ((continuous_cTransform hv).comp continuous_fst).add
      (((continuous_fst.dist continuous_snd).pow 2).div_const 2 |>.div_const t)
  · exact hmtw.active_hull_strict_local_min hv hp ht ht1 hID

end WeakMTWTransport

end

end OAI
