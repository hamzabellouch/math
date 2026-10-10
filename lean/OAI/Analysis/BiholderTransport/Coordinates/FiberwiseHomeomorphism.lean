import Mathlib

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

namespace WeakMTWTransport
section FiberwiseHomeomorphism
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def fiberwiseHomeomorph (e : OpenPartialHomeomorph (X × Y) (X × Y))
    (he : ∀ z : X × Y, (e z).1 = z.1) (x : X) : OpenPartialHomeomorph Y Y where
  toFun y := (e (x,y)).2
  invFun y := (e.symm (x,y)).2
  source := {y | (x,y) ∈ e.source}
  target := {y | (x,y) ∈ e.target}
  map_source' := by
    intro y hy
    change (x,(e (x,y)).2) ∈ e.target
    have h : (x,(e (x,y)).2) = e (x,y) := Prod.ext (he (x,y)).symm rfl
    rw [h]
    exact e.map_source hy
  map_target' := by
    intro y hy
    have hx : (e.symm (x,y)).1 = x := (he _).symm.trans (congrArg Prod.fst (e.right_inv hy))
    change (x,(e.symm (x,y)).2) ∈ e.source
    have h : (x,(e.symm (x,y)).2) = e.symm (x,y) := Prod.ext hx.symm rfl
    rw [h]
    exact e.map_target hy
  left_inv' := by
    intro y hy
    have h : (x,(e (x,y)).2) = e (x,y) := Prod.ext (he (x,y)).symm rfl
    change (e.symm (x,(e (x,y)).2)).2 = y
    rw [h,e.left_inv hy]
  right_inv' := by
    intro y hy
    have hx : (e.symm (x,y)).1 = x := (he _).symm.trans (congrArg Prod.fst (e.right_inv hy))
    have h : (x,(e.symm (x,y)).2) = e.symm (x,y) := Prod.ext hx.symm rfl
    change (e (x,(e.symm (x,y)).2)).2 = y
    rw [h,e.right_inv hy]
  continuousOn_toFun := (e.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun _ h => h)).snd
  continuousOn_invFun := (e.symm.continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn (fun _ h => h)).snd
  open_source := e.open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)

end FiberwiseHomeomorphism

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma fiberwiseHomeomorph_contDiffOn
    {e : OpenPartialHomeomorph (E × F) (E × F)}
    (he : ∀ z : E × F, (e z).1 = z.1) (x : E)
    (hsm : ContDiffOn ℝ ∞ e e.source) :
    ContDiffOn ℝ ∞ (fiberwiseHomeomorph e he x) (fiberwiseHomeomorph e he x).source :=
  (hsm.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ h => h)).snd

lemma fiberwiseHomeomorph_symm_contDiffOn
    {e : OpenPartialHomeomorph (E × F) (E × F)}
    (he : ∀ z : E × F, (e z).1 = z.1) (x : E)
    (hsm : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (fiberwiseHomeomorph e he x).symm (fiberwiseHomeomorph e he x).target :=
  (hsm.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ h => h)).snd

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

lemma first_coordinate_preserving_derivative_invertible {f : E × F → F} {x : E} {v : F}
    (hf : DifferentiableAt ℝ f (x,v))
    (hi : (fderiv ℝ (fun w => f (x,w)) v).IsInvertible) :
    (fderiv ℝ (fun z : E × F => (z.1,f z)) (x,v)).IsInvertible := by
  let L := fderiv ℝ (fun z : E × F => (z.1,f z)) (x,v)
  have hL : L = (ContinuousLinearMap.fst ℝ E F).prod (fderiv ℝ f (x,v)) :=
    ((ContinuousLinearMap.fst ℝ E F).hasFDerivAt.prodMk hf.hasFDerivAt).fderiv
  have hpart : fderiv ℝ (fun w => f (x,w)) v =
      (fderiv ℝ f (x,v)).comp (ContinuousLinearMap.inr ℝ E F) :=
    (hf.hasFDerivAt.comp v ((hasFDerivAt_const x v).prodMk (hasFDerivAt_id v))).fderiv
  have hinj : Function.Injective L := by
    intro a b hab
    have hd : L (a-b) = 0 := by rw [map_sub,hab,sub_self]
    have hx : a.1-b.1 = 0 := by
      have h := congrArg Prod.fst hd
      rw [hL] at h
      exact h
    have hv : a.2-b.2 = 0 := by
      apply hi.injective
      have h := congrArg Prod.snd hd
      have hz : a-b = (0,a.2-b.2) := Prod.ext hx rfl
      change (fderiv ℝ (fun w => f (x,w)) v) (a.2-b.2) =
        (fderiv ℝ (fun w => f (x,w)) v) 0
      rw [map_zero,hpart]
      rw [hL,hz] at h
      exact h
    exact Prod.ext (sub_eq_zero.mp hx) (sub_eq_zero.mp hv)
  have hsur : Function.Surjective L := LinearMap.injective_iff_surjective.mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsur),rfl⟩

end WeakMTWTransport

end

end OAI
