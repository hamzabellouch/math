import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.FirstCutSegment

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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.convex_nonconjugate_subset (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {C : Set (TangentSpace 𝓘(ℝ,Model n) x)}
    (hC : Convex ℝ C) (hmin : C ⊆ minimizingVectors x) :
    Convex ℝ {p | p ∈ C ∧ Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p)} := by
  intro u hu v hv a b ha hb hab
  refine ⟨hC hu.1 hv.1 ha hb hab,?_⟩
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    simpa only [ha0,hb1,zero_smul,zero_add,one_smul] using hv.2
  by_cases hb0 : b=0
  · have ha1 : a=1 := by linarith
    simpa only [hb0,ha1,zero_smul,add_zero,one_smul] using hu.2
  by_cases huv : u=v
  · have heq : a • u+b • v=v := by rw [huv,←add_smul,hab,one_smul]
    rw [heq]
    exact hv.2
  let p := a • u+b • v
  let e := v-u
  have he : e≠0 := sub_ne_zero.mpr (Ne.symm huv)
  have hleftEq : p+(-b) • e=u := by
    dsimp [p,e]
    rw [show a=1-b by linarith]
    module
  have hrightEq : p+a • e=v := by
    dsimp [p,e]
    rw [show b=1-a by linarith]
    module
  have hseg : ∀ s ∈ Icc (-b) a, p+s • e ∈ minimizingVectors x := by
    intro s hs
    have hq : p+s • e=(a-s) • u+(b+s) • v := by dsimp [p,e]; module
    rw [hq]
    exact hmin (hC hu.1 hv.1 (sub_nonneg.mpr hs.2) (by linarith [hs.1]) (by linarith))
  have hleft : Function.Injective (fderiv ℝ (fun w => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+(-b) • e)) (riemannianExp x w)) (p+(-b) • e)) := by
    rw [hleftEq]
    exact hu.2
  have hright : Function.Injective (fderiv ℝ (fun w => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x (p+a • e)) (riemannianExp x w)) (p+a • e)) := by
    rw [hrightEq]
    exact hv.2
  let D := fderiv ℝ (fun w => extChartAt 𝓘(ℝ,Model n) (riemannianExp x p) (riemannianExp x w)) p
  have hzero (k) (hk : D k=0) : k=0 := by
    apply hmtw.firstcut_segment_kernel_zero (neg_neg_iff_pos.mpr (lt_of_le_of_ne hb (Ne.symm hb0)))
      (lt_of_le_of_ne ha (Ne.symm ha0)) he hseg hleft hright
    rw [exp_mfderiv_apply_eq_coordinate]
    exact hk
  intro k l hkl
  apply sub_eq_zero.mp
  apply hzero (k-l)
  rw [map_sub,hkl,sub_self]

lemma WeakMTW.convexHull_nonconjugate (hmtw : WeakMTW (n := n) (M := M))
    {x : M} {S : Set (TangentSpace 𝓘(ℝ,Model n) x)}
    (hmin : convexHull ℝ S ⊆ minimizingVectors x)
    (hreg : ∀ p ∈ S, Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p))
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p ∈ convexHull ℝ S) :
    Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp x p) (riemannianExp x v)) p) := by
  have hsub : S ⊆ {q | q ∈ convexHull ℝ S ∧ Function.Injective (fderiv ℝ (fun v =>
      extChartAt 𝓘(ℝ,Model n) (riemannianExp x q) (riemannianExp x v)) q)} :=
    fun q hq => ⟨subset_convexHull ℝ S hq,hreg q hq⟩
  exact (convexHull_min hsub (hmtw.convex_nonconjugate_subset (convex_convexHull ℝ S) hmin) hp).2
end WeakMTWTransport

end

end OAI
