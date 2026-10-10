import Mathlib
import OAI.Analysis.WeakInfiniteness.AlgebraicTensorSpan
import OAI.Analysis.WeakInfiniteness.TensorCut
import OAI.Analysis.WeakInfiniteness.UniformKernelConvergence

namespace OAI

universe u v

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

namespace WeakPureInfiniteness

open Filter Topology

section TensorIdealCut

variable {A : Type u} {C D : Type v} [CStarAlgebra A]
  [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra D]

def kernelAlgebra (q : C →⋆ₙₐ[ℂ] D) : NonUnitalStarSubalgebra ℂ C where
  carrier := {c | q c = 0}
  zero_mem' := map_zero q
  add_mem' hx hy := by change q (_+_) = 0; rw [map_add,hx,hy,add_zero]
  mul_mem' hx _ := by change q (_*_) = 0; rw [map_mul,hx,zero_mul]
  smul_mem' c _ hx := by change q (c • _) = 0; rw [map_smul,hx,smul_zero]
  star_mem' hx := by change q (star _) = 0; rw [map_star,hx,star_zero]

lemma kernelAlgebra_closed (q : C →⋆ₙₐ[ℂ] D) : IsClosed (kernelAlgebra q : Set C) :=
  isClosed_eq (nonUnitalStarHom_continuous q) continuous_const

instance (q : C →⋆ₙₐ[ℂ] D) : NonUnitalCStarAlgebra (kernelAlgebra q) := by
  letI := kernelAlgebra_closed q
  infer_instance

def tensorCutLinear (e : C) : MinimalTensor A C →ₗ[ℂ] MinimalTensor A C where
  toFun := tensorCut e
  map_add' x y := by simp [tensorCut,add_mul,add_sub_add_comm]
  map_smul' c x := by simp [tensorCut,smul_mul_assoc,smul_sub]

def cutVanishingSpace {ι : Type*} (l : Filter ι) (e : ι → C) :
    Submodule ℂ (MinimalTensor A C) where
  carrier := {x | Tendsto (fun i => tensorCut (e i) x) l (𝓝 0)}
  zero_mem' := by simpa [tensorCut] using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : MinimalTensor A C)) l (𝓝 0))
  add_mem' hx hy := by
    change Tendsto _ _ _
    have hadd (i) (x y : MinimalTensor A C) :
        tensorCut (e i) (x+y) = tensorCut (e i) x + tensorCut (e i) y :=
      (tensorCutLinear (e i)).map_add x y
    simp only [hadd]
    simpa only [add_zero] using hx.add hy
  smul_mem' c x hx := by
    change Tendsto _ _ _
    have hsmul (i) (y : MinimalTensor A C) :
        tensorCut (e i) (c • y) = c • tensorCut (e i) y :=
      (tensorCutLinear (e i)).map_smul c y
    simp only [hsmul]
    simpa only [smul_zero] using hx.const_smul c

lemma cutVanishingSpace_closed [PartialOrder C] [StarOrderedRing C]
    {ι : Type*} (l : Filter ι) (e : ι → C)
    (he : ∀ᶠ i in l, 0 ≤ e i ∧ ‖e i‖ ≤ 1) :
    IsClosed (cutVanishingSpace (A := A) l e : Set (MinimalTensor A C)) := by
  apply isClosed_setOf_tendsto_zero_of_bound l (fun i => tensorCutLinear (e i))
  filter_upwards [he] with i hi
  exact norm_tensorCut_le (e i) hi.1 hi.2

lemma tensorCut_tendsto_zero_on_ideal [PartialOrder C] [StarOrderedRing C]
    {ι : Type*} (l : Filter ι) (e : ι → C)
    (he : ∀ᶠ i in l, 0 ≤ e i ∧ ‖e i‖ ≤ 1)
    (q : C →⋆ₙₐ[ℂ] D)
    (happ : ∀ c : C, q c = 0 → Tendsto (fun i => c * e i) l (𝓝 c))
    (x : MinimalTensor A C) (hx : x.val ∈ tensorKernelIdeal (A := A) q) :
    Tendsto (fun i => tensorCut (e i) x) l (𝓝 0) := by
  let S := cutVanishingSpace (A := A) l e
  let j : MinimalTensor A C →ₗ[ℂ] SpatialAmbient A C :=
    { toFun := Subtype.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let T := S.map j
  have hTc : IsClosed (T : Set (SpatialAmbient A C)) :=
    isClosed_closure.isClosedMap_subtype_val _ (cutVanishingSpace_closed l e he)
  have hgen : ∀ a c, q c = 0 → spatialElementary a c ∈ T := by
    intro a c hc
    refine ⟨minimalElementary a c, ?_, rfl⟩
    change Tendsto (fun i => tensorCut (e i) (minimalElementary a c)) l (𝓝 0)
    simp only [tensorCut_elementary]
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

end TensorIdealCut

end WeakPureInfiniteness
end

end OAI
