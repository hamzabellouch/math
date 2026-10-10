import Mathlib
import OAI.Analysis.BiholderTransport.Contact.GraphProjection

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

lemma exists_minimizing_graph_point {u : M → ℝ} (hu : Continuous u)
    {t : ℝ} (ht : 0<t) (y : M) :
    ∃ z : subgradientGraph (n := n) u, graphProjection u t z=y ∧
      t • z.1.2∈minimizingVectors z.1.1 ∧
      ∀ a : M, u z.1.1+cost z.1.1 y/t≤u a+cost a y/t := by
  let : Nonempty M := ⟨y⟩
  obtain ⟨x,_,hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (hu.add ((continuous_cost_left y).div_const t)).continuousOn
  obtain ⟨p,hp,hpy⟩ := exists_minimizing_vector (n := n) x y
  have hsub := global_min_divided_cost_subgradient hp ht
    (show ∀ z : M, u x+cost x (riemannianExp x p)/t≤
      u z+cost z (riemannianExp x p)/t by
      intro z
      rw [hpy]
      exact hmin (mem_univ z))
  refine ⟨⟨⟨x,t⁻¹ • p⟩,hsub⟩,?_,?_,fun a => hmin (mem_univ a)⟩
  · dsimp only [graphProjection]
    rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul,hpy]
  · simpa only [smul_smul,mul_inv_cancel₀ ht.ne',one_smul] using hp

lemma global_min_of_injective_graphProjection {u : M → ℝ} (hu : Continuous u)
    {t : ℝ} (ht : 0<t) (hinj : Function.Injective (graphProjection (n := n) u t))
    (z : subgradientGraph (n := n) u) :
    t • z.1.2∈minimizingVectors z.1.1 ∧
      ∀ a : M, u z.1.1+cost z.1.1 (graphProjection u t z)/t≤
        u a+cost a (graphProjection u t z)/t := by
  obtain ⟨w,hw,hmin,hglobal⟩ := exists_minimizing_graph_point (n := n) hu ht (graphProjection u t z)
  have he : w=z := hinj hw
  subst w
  exact ⟨hmin,hglobal⟩

lemma unique_minimizing_direction_of_injective_graphProjection {u : M → ℝ}
    {t : ℝ} (ht : 0<t) (hinj : Function.Injective (graphProjection (n := n) u t))
    (z : subgradientGraph (n := n) u)
    (hmin : ∀ a : M, u z.1.1+cost z.1.1 (graphProjection u t z)/t≤
      u a+cost a (graphProjection u t z)/t)
    {q : TangentSpace 𝓘(ℝ,Model n) z.1.1} (hq : q∈minimizingVectors z.1.1)
    (hqe : riemannianExp z.1.1 q=graphProjection u t z) : q=t • z.1.2 := by
  have hsub := global_min_divided_cost_subgradient hq ht
    (show ∀ a : M, u z.1.1+cost z.1.1 (riemannianExp z.1.1 q)/t≤
      u a+cost a (riemannianExp z.1.1 q)/t by simpa only [hqe] using hmin)
  let w : subgradientGraph (n := n) u := ⟨⟨z.1.1,t⁻¹ • q⟩,hsub⟩
  have hw : graphProjection u t w=graphProjection u t z := by
    dsimp only [graphProjection,w]
    rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
    exact hqe
  have he : w=z := hinj hw
  have heval := congrArg Subtype.val he
  have hp : t⁻¹ • q=z.1.2 := by
    exact TotalSpace.mk_injective z.1.1 heval
  calc
    q = t • (t⁻¹ • q) := by rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
    _ = t • z.1.2 := congrArg (t • ·) hp

end WeakMTWTransport

end

end OAI
