import Mathlib
import OAI.Analysis.WeakInfiniteness.TensorMultiplier
import OAI.Analysis.WeakInfiniteness.UniformKernelConvergence

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

universe u v

noncomputable section

open Filter Topology

variable {A B : Type u} {C D : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def tensorCutNonunitalLinear (e : C) : MinimalTensor A C →ₗ[ℂ] MinimalTensor A C where
  toFun := tensorCutNonunital e
  map_add' x y := by apply Subtype.ext; change (x.val+y.val)-(x.val+y.val)*_=(_-_*_)+(_-_*_); rw [add_mul,add_sub_add_comm]
  map_smul' c x := by apply Subtype.ext; change c • x.val-(c • x.val)*_ = c • (x.val-x.val*_); rw [smul_mul_assoc,smul_sub]

def cutVanishingSpaceNonunital {ι : Type*} (l : Filter ι) (e : ι → C) :
    Submodule ℂ (MinimalTensor A C) where
  carrier := {x | Tendsto (fun i => tensorCutNonunital (e i) x) l (𝓝 0)}
  zero_mem' := by
    change Tendsto (fun i => tensorCutNonunital (e i) (0 : MinimalTensor A C)) l (𝓝 0)
    have hz (e : C) : tensorCutNonunital e (0 : MinimalTensor A C)=0 :=
      Subtype.ext (by change 0-0*_=0; simp)
    simp only [hz]
    exact tendsto_const_nhds
  add_mem' hx hy := by
    change Tendsto _ _ _
    have hadd (i) (x y : MinimalTensor A C) :
        tensorCutNonunital (e i) (x+y) = tensorCutNonunital (e i) x + tensorCutNonunital (e i) y :=
      (tensorCutNonunitalLinear (e i)).map_add x y
    simp only [hadd]
    simpa only [add_zero] using hx.add hy
  smul_mem' c x hx := by
    change Tendsto _ _ _
    have hsmul (i) (y : MinimalTensor A C) :
        tensorCutNonunital (e i) (c • y) = c • tensorCutNonunital (e i) y :=
      (tensorCutNonunitalLinear (e i)).map_smul c y
    simp only [hsmul]
    simpa only [smul_zero] using hx.const_smul c

lemma cutVanishingSpaceNonunital_closed [PartialOrder C] [StarOrderedRing C]
    {ι : Type*} (l : Filter ι) (e : ι → C)
    (he : ∀ᶠ i in l, 0 ≤ e i ∧ ‖e i‖ ≤ 1) :
    IsClosed (cutVanishingSpaceNonunital (A := A) l e : Set (MinimalTensor A C)) := by
  apply isClosed_setOf_tendsto_zero_of_bound l (fun i => tensorCutNonunitalLinear (e i))
  filter_upwards [he] with i hi
  exact norm_tensorCutNonunital_le (e i) hi.1 hi.2

lemma tensorCutNonunital_tendsto_zero_on_ideal [PartialOrder C] [StarOrderedRing C]
    {ι : Type*} (l : Filter ι) (e : ι → C)
    (he : ∀ᶠ i in l, 0 ≤ e i ∧ ‖e i‖ ≤ 1)
    (q : C →⋆ₙₐ[ℂ] D)
    (happ : ∀ c : C, q c = 0 → Tendsto (fun i => c * e i) l (𝓝 c))
    (x : MinimalTensor A C) (hx : x.val ∈ tensorKernelIdeal (A := A) q) :
    Tendsto (fun i => tensorCutNonunital (e i) x) l (𝓝 0) := by
  let S := cutVanishingSpaceNonunital (A := A) l e
  let j : MinimalTensor A C →ₗ[ℂ] SpatialAmbient A C :=
    { toFun := Subtype.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let T := S.map j
  have hTc : IsClosed (T : Set (SpatialAmbient A C)) :=
    isClosed_closure.isClosedMap_subtype_val _ (cutVanishingSpaceNonunital_closed l e he)
  have hgen : ∀ a c, q c = 0 → spatialElementary a c ∈ T := by
    intro a c hc
    refine ⟨minimalElementary a c, ?_, rfl⟩
    change Tendsto (fun i => tensorCutNonunital (e i) (minimalElementary a c)) l (𝓝 0)
    simp only [tensorCutNonunital_elementary]
    let F : C →L[ℂ] MinimalTensor A C :=
      LinearMap.mkContinuous
        { toFun c := minimalElementary a c
          map_add' c d := Subtype.ext (spatialElementary_add_right a c d)
          map_smul' r c := Subtype.ext (spatialElementary_smul_right r a c) }
        ‖a‖ (norm_spatialElementary_le a)
    have hh : Tendsto (fun i => c-c*e i) l (𝓝 0) := by
      simpa only [sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => c) l (𝓝 c)).sub (happ c hc)
    have hF (b : C) : F b = minimalElementary a b := rfl
    have h := F.continuous.tendsto 0 |>.comp hh
    simp only [Function.comp_def, hF] at h
    have hz : minimalElementary a (0 : C) = (0 : MinimalTensor A C) := map_zero F
    exact hz ▸ h
  have hspan : Submodule.span ℂ
      {z : SpatialAmbient A C | ∃ a : A, ∃ c : C, q c = 0 ∧ z = spatialElementary a c} ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,c,hc,rfl⟩
    exact hgen a c hc
  change x.val ∈ (tensorKernelIdeal (A := A) q : Set (SpatialAmbient A C)) at hx
  rw [tensorKernelIdeal_eq_closure_span] at hx
  have hmem : x.val ∈ T := (closure_minimal hspan hTc) hx
  obtain ⟨y,hy,hyx⟩ := hmem
  have hyx' : y = x := Subtype.ext hyx
  exact hyx' ▸ hy

lemma tensorRightMultiply_kernel_mem (q : C →⋆ₙₐ[ℂ] D) (e : C) (he : q e=0)
    (x : MinimalTensor A C) :
    (tensorRightMultiply e x).val ∈ tensorKernelIdeal (A := A) q := by
  have hs : ∀ z ∈ Submodule.span ℂ
      (Set.range fun p : A × C => spatialElementary p.1 p.2),
      z*spatialRightMultiplier e ∈ tensorKernelIdeal (A := A) q := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨a,c⟩,rfl⟩ := hz
      rw [spatialElementary_mul_rightMultiplier]
      apply NonUnitalStarSubalgebra.le_topologicalClosure
      apply NonUnitalStarAlgebra.subset_adjoin ℂ
      exact ⟨a,c*e,by rw [map_mul,he,mul_zero],rfl⟩
    | zero => rw [zero_mul]; exact (tensorKernelIdeal (A := A) q).zero_mem
    | add z w _ _ hz hw => rw [add_mul]; exact (tensorKernelIdeal (A := A) q).add_mem hz hw
    | smul c z _ hz => rw [smul_mul_assoc]; exact (tensorKernelIdeal (A := A) q).smul_mem c hz
  have hc : IsClosed {z : SpatialAmbient A C | z*spatialRightMultiplier e ∈ tensorKernelIdeal (A := A) q} :=
    isClosed_closure.preimage (continuous_id.mul continuous_const)
  have hx := x.property
  change x.val ∈ (minimalTensorSubalgebra A C : Set (SpatialAmbient A C)) at hx
  rw [minimalTensor_eq_closure_span] at hx
  exact (closure_minimal hs hc) hx

lemma tensor_mem_ideal_of_nonunitalCuts {ι : Type*} (l : Filter ι) [l.NeBot]
    (e : ι → C) (q : C →⋆ₙₐ[ℂ] D) (he : ∀ i, q (e i)=0)
    (x : MinimalTensor A C)
    (hx : Tendsto (fun i => tensorCutNonunital (e i) x) l (𝓝 0)) :
    x.val ∈ tensorKernelIdeal (A := A) q := by
  have hmul : Tendsto (fun i => tensorRightMultiply (e i) x) l (𝓝 x) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ι => x) l (𝓝 x)).sub hx
    simpa only [tensorCutNonunital, sub_sub_cancel, sub_zero] using h
  apply isClosed_closure.mem_of_tendsto (continuous_subtype_val.tendsto x |>.comp hmul)
  exact Filter.Eventually.of_forall (fun i => tensorRightMultiply_kernel_mem q (e i) (he i) x)

end

end WeakPureInfiniteness
end

end OAI
