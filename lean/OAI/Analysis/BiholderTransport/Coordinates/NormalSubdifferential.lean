import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.ActiveHull

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

namespace WeakMTWTransport

lemma hasFDerivAt_affine_lower_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {D : E →L[ℝ] ℝ} (hD : HasFDerivAt f D 0) :
    ∀ ε>0, ∀ᶠ h : E in 𝓝 0, D h-ε*‖h‖≤f h-f 0 := by
  intro ε hε
  have H := hD.isLittleO.bound hε
  filter_upwards [H] with h hh
  simp only [sub_zero,Real.norm_eq_abs] at hh
  linarith [(abs_le.mp hh).1]

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Model n) M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

def normalSubdifferential (u : M → ℝ) (x : M) : Set (TangentSpace 𝓘(ℝ,Model n) x) :=
  {p | ∀ ε>0, ∀ᶠ h : TangentSpace 𝓘(ℝ,Model n) x in 𝓝 0,
    inner ℝ p h-ε*‖h‖≤u (riemannianExp x h)-u x}

lemma convex_normalSubdifferential (u : M → ℝ) (x : M) :
    Convex ℝ (normalSubdifferential (n := n) u x) := by
  intro p hp q hq a b ha hb hab ε hε
  filter_upwards [hp ε hε,hq ε hε] with h hh hk
  calc
    inner ℝ (a • p+b • q) h-ε*‖h‖ =
        a*(inner ℝ p h-ε*‖h‖)+b*(inner ℝ q h-ε*‖h‖) := by
      simp only [inner_add_left,real_inner_smul_left,mul_sub]
      have he := congrArg (fun r : ℝ => r*(ε*‖h‖)) hab
      nlinarith [he]
    _ ≤ a*(u (riemannianExp x h)-u x)+b*(u (riemannianExp x h)-u x) :=
      add_le_add (mul_le_mul_of_nonneg_left hh ha) (mul_le_mul_of_nonneg_left hk hb)
    _ = u (riemannianExp x h)-u x := by rw [←add_mul,hab,one_mul]

variable [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma activeLogs_subset_normalSubdifferential {v : M → ℝ} (hv : Continuous v) (x : M) :
    activeLogs (n := n) v x ⊆ normalSubdifferential (cTransform v) x := by
  intro p hp
  have hID := contracted_minimizer_mem_injectivityDomain hp.1
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  let f := fun h : TangentSpace 𝓘(ℝ,Model n) x =>
    (-2:ℝ)*(normalCost x ((1/2:ℝ) • p) h-normalCost x ((1/2:ℝ) • p) 0)
  have hD : HasFDerivAt f (innerSL ℝ p) 0 := by
    apply (((normalCost_hasFDerivAt_zero hID).sub_const
      (normalCost x ((1/2:ℝ) • p) 0)).const_smul (-2:ℝ)).congr_fderiv
    ext h
    simp only [smul_apply,innerSL_apply_apply,inner_neg_left,real_inner_smul_left,smul_eq_mul]
    ring
  intro ε hε
  filter_upwards [hasFDerivAt_affine_lower_support hD ε hε] with h hh
  have hs := active_split_lower_support hv hp.1 hp.2
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num) (riemannianExp x h)
  have hf0 : f 0=0 := by simp [f]
  rw [hf0,sub_zero] at hh
  simp only [innerSL_apply_apply] at hh
  apply hh.trans
  have he : f h = -(cost (riemannianExp x h) (riemannianExp x ((1/2:ℝ) • p)) -
      cost x (riemannianExp x ((1/2:ℝ) • p))) / (1/2:ℝ) := by
    dsimp [f,normalCost]
    rw [riemannianExp_zero]
    ring
  rw [he]
  exact hs

lemma active_hull_subset_normalSubdifferential {v : M → ℝ} (hv : Continuous v) (x : M) :
    convexHull ℝ (activeLogs (n := n) v x) ⊆ normalSubdifferential (cTransform v) x :=
  convexHull_min (activeLogs_subset_normalSubdifferential hv x)
    (convex_normalSubdifferential (cTransform v) x)

end WeakMTWTransport

end

end OAI
