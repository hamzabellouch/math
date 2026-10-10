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

namespace WeakMTWTransport
universe u w
variable {K : Type w} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance pathCalculusNormedAddCommGroupContinuousLinearMap :
    NormedAddCommGroup (E →L[ℝ] F) := ContinuousLinearMap.toNormedAddCommGroup
local instance pathCalculusNormedSpaceContinuousLinearMap :
    NormedSpace ℝ (E →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
local instance pathCalculusNormedAddCommGroupContinuousMap :
    NormedAddCommGroup C(K,E →L[ℝ] F) := ContinuousMap.instNormedAddCommGroup

def pathLinearApply (A : C(K,E →L[ℝ] F)) : C(K,E) →L[ℝ] C(K,F) := by
  let L : C(K,E) →ₗ[ℝ] C(K,F) :=
    { toFun := fun u => ⟨fun t => A t (u t),A.continuous.clm_apply u.continuous⟩
      map_add' := by intro u v; ext t; exact map_add (A t) (u t) (v t)
      map_smul' := by intro c u; ext t; exact map_smul (A t) c (u t) }
  exact L.mkContinuous ‖A‖ (by
      intro u
      change ‖(⟨fun t => A t (u t),A.continuous.clm_apply u.continuous⟩ : C(K,F))‖ ≤ ‖A‖ * ‖u‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
      intro t
      exact (A t).le_opNorm (u t) |>.trans
        (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] lemma pathLinearApply_apply (A : C(K,E →L[ℝ] F)) (u : C(K,E)) (t : K) :
    pathLinearApply A u t = A t (u t) := rfl

lemma norm_pathLinearApply_le (A : C(K,E →L[ℝ] F)) : ‖pathLinearApply A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
  intro t
  exact (A t).le_opNorm (u t) |>.trans
    (mul_le_mul (A.norm_coe_le_norm t) (u.norm_coe_le_norm t)
      (norm_nonneg _) (norm_nonneg _))

def pathLinearApplyL : C(K,E →L[ℝ] F) →L[ℝ] C(K,E) →L[ℝ] C(K,F) := by
  let L : C(K,E →L[ℝ] F) →ₗ[ℝ] C(K,E) →L[ℝ] C(K,F) :=
    { toFun := fun (A : C(K,E →L[ℝ] F)) => pathLinearApply A
      map_add' := by intro A B; ext u t; rfl
      map_smul' := by intro c A; ext u t; rfl }
  refine LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := C(K,E →L[ℝ] F)) (F := C(K,E) →L[ℝ] C(K,F)) L 1 ?_
  intro A
  change ‖pathLinearApply A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using norm_pathLinearApply_le A

lemma hasFDerivAt_path_comp (f : C(E,F)) (f' : C(E,E →L[ℝ] F))
    (hder : ∀ x, HasFDerivAt f (f' x) x) (u : C(K,E)) :
    HasFDerivAt (fun v : C(K,E) => f.comp v) (pathLinearApply (f'.comp u)) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  have hc : IsCompact (range u) := isCompact_range u.continuous
  have huni := hc.uniformContinuousAt_of_continuousAt f'
    (fun _ _ => f'.continuous.continuousAt)
    (r := {z : (E →L[ℝ] F) × (E →L[ℝ] F) | dist z.1 z.2 < ε})
    (Metric.mem_uniformity_dist.mpr ⟨ε,hε,fun {_ _} h => h⟩)
  obtain ⟨δ,hδ,hclose⟩ := Metric.mem_uniformity_dist.mp huni
  filter_upwards [Metric.ball_mem_nhds (0:C(K,E)) hδ] with v hv
  have hvnorm : ‖v‖ < δ := by simpa using hv
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg v))).mpr
  intro t
  have hbound : ∀ z ∈ Metric.ball (u t) δ, ‖f' z - f' (u t)‖ ≤ ε := by
    intro z hz
    have hh := hclose (by simpa only [Metric.mem_ball,dist_comm] using hz) (mem_range_self t)
    change dist (f' (u t)) (f' z) < ε at hh
    exact le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hh)
  have hb : u t + v t ∈ Metric.ball (u t) δ := by
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left]
    exact (v.norm_coe_le_norm t).trans_lt hvnorm
  have hm := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z (_ : z ∈ Metric.ball (u t) δ) => (hder z).hasFDerivWithinAt)
    hbound (convex_ball (u t) δ) (Metric.mem_ball_self hδ) hb
  have heq : ((f.comp (u+v) - f.comp u - pathLinearApply (f'.comp u) v) t) =
      f (u t + v t) - f (u t) - f' (u t) ((u t + v t) - u t) := by
    simp only [ContinuousMap.sub_apply,ContinuousMap.comp_apply,ContinuousMap.add_apply,
      pathLinearApply_apply,add_sub_cancel_left]
  rw [heq]
  exact hm.trans (by simpa only [add_sub_cancel_left] using
    mul_le_mul_of_nonneg_left (v.norm_coe_le_norm t) hε.le)

lemma contDiff_path_comp_nat (m : ℕ) (f : C(E,F)) (hf : ContDiff ℝ m f) :
    ContDiff ℝ m (fun v : C(K,E) => f.comp v) := by
  induction m generalizing F with
  | zero => exact contDiff_zero.mpr f.continuous_postcomp
  | succ m ih =>
    obtain ⟨f',hf',hder⟩ := contDiff_succ_iff_hasFDerivAt.mp hf
    let F' : C(E,E →L[ℝ] F) := ⟨f',hf'.continuous⟩
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun v => pathLinearApply (F'.comp v),?_,?_⟩
    · exact (pathLinearApplyL (K := K) (E := E) (F := F)).contDiff.comp
        (ih F' hf')
    · intro u; exact hasFDerivAt_path_comp f F' hder u

lemma contDiff_path_comp (f : C(E,F)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun v : C(K,E) => f.comp v) :=
  contDiff_infty.mpr fun m => contDiff_path_comp_nat m f (contDiff_infty.mp hf m)

end WeakMTWTransport

end

end OAI
