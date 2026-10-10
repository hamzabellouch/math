import Mathlib
import OAI.Geometry.SmoothYau.Estimates.PathExtension

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
universe u v
variable {K : Type v} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance superpositionMapNorm : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance superpositionMapSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance superpositionContinuousNorm : NormedAddCommGroup C(K, E) := inferInstance
local instance superpositionContinuousSpace : NormedSpace ℝ C(K, E) := inferInstance
local instance superpositionContinuousMapNorm : NormedAddCommGroup C(K, E →L[ℝ] F) := inferInstance
local instance superpositionContinuousMapSpace : NormedSpace ℝ C(K, E →L[ℝ] F) := inferInstance

def continuousMapApply (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) := by
  let L : C(K, E) →ₗ[ℝ] C(K, F) :=
    { toFun := fun u => ⟨fun x => A x (u x), A.continuous.clm_apply u.continuous⟩
      map_add' := fun u v => by ext x; exact map_add (A x) (u x) (v x)
      map_smul' := fun c u => by ext x; exact map_smul (A x) c (u x) }
  exact L.mkContinuous ‖A‖ (fun u =>
    (ContinuousMap.norm_le (L u) (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
      (fun x => ((A x).le_opNorm (u x)).trans
        (mul_le_mul (A.norm_coe_le_norm x) (u.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _))))

@[simp] lemma continuousMapApply_apply (A : C(K, E →L[ℝ] F)) (u : C(K, E)) (x : K) :
    continuousMapApply A u x = A x (u x) := rfl

lemma continuousMapApply_norm_le (A : C(K, E →L[ℝ] F)) :
    ‖continuousMapApply A‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) (fun u =>
    (ContinuousMap.norm_le (continuousMapApply A u) (mul_nonneg (norm_nonneg A) (norm_nonneg u))).mpr
      (fun x => ((A x).le_opNorm (u x)).trans
        (mul_le_mul (A.norm_coe_le_norm x) (u.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _))))

def continuousMapApplyCLM : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) := by
  let L : C(K, E →L[ℝ] F) →ₗ[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
    { toFun := continuousMapApply
      map_add' := fun A B => by ext u x; rfl
      map_smul' := fun c A => by ext u x; rfl }
  refine LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := C(K, E →L[ℝ] F)) (F := C(K, E) →L[ℝ] C(K, F)) L 1 ?_
  intro A
  change ‖continuousMapApply A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using continuousMapApply_norm_le A

def superposition (f : E → F) (hf : Continuous f) : C(K, E) → C(K, F) :=
  fun u => ⟨f ∘ u, hf.comp u.continuous⟩

omit [CompactSpace K] [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] lemma superposition_apply (f : E → F) (hf : Continuous f) (u : C(K, E)) (x : K) :
    superposition f hf u x = f (u x) := rfl

variable [FiniteDimensional ℝ E]

lemma hasFDerivAt_superposition {f : E → F} (hf : ContDiff ℝ ∞ f) (u : C(K, E)) :
    HasFDerivAt (superposition f hf.continuous)
      (continuousMapApply ⟨(fderiv ℝ f) ∘ u, (hf.continuous_fderiv (by simp)).comp u.continuous⟩) u := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have huc := (isCompact_closedBall (0 : E) (‖u‖ + 1)).uniformContinuousOn_of_continuous
    (hf.continuous_fderiv (by simp)).continuousOn
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  let r := min δ 1
  have hr : 0 < r := lt_min hδ zero_lt_one
  filter_upwards [continuous_norm.continuousAt.eventually_lt_const
    (show ‖(0 : C(K, E))‖ < r by simpa using hr)] with h hh
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro x
  have hx : u x ∈ closedBall (0 : E) (‖u‖ + 1) := by
    rw [mem_closedBall, dist_zero_right]
    exact (u.norm_coe_le_norm x).trans (le_add_of_nonneg_right zero_le_one)
  have hs : ball (u x) r ⊆ closedBall (0 : E) (‖u‖ + 1) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    calc ‖y‖ ≤ ‖y - u x‖ + ‖u x‖ := by simpa only [add_comm] using norm_le_insert' y (u x)
         _ ≤ 1 + ‖u‖ := add_le_add (by simpa only [dist_eq_norm] using (mem_ball.mp hy).le.trans (min_le_right δ 1))
           (u.norm_coe_le_norm x)
         _ = ‖u‖ + 1 := add_comm _ _
  have hderiv : ∀ y ∈ ball (u x) r, ‖fderiv ℝ f y - fderiv ℝ f (u x)‖ ≤ ε := by
    intro y hy
    simpa only [dist_eq_norm] using (hbound y (hs hy) (u x) hx
      ((mem_ball.mp hy).trans_le (min_le_left _ _))).le
  have hhx : u x + h x ∈ ball (u x) r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (h.norm_coe_le_norm x).trans_lt hh
  have hb := (convex_ball (u x) r).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hf.differentiable (by simp) y) hderiv (mem_ball_self hr) hhx
  simpa only [ContinuousMap.sub_apply, ContinuousMap.add_apply, superposition_apply,
      continuousMapApply_apply, ContinuousMap.coe_mk, Function.comp_apply, add_sub_cancel_left]
    using (by simpa only [add_sub_cancel_left] using hb :
      ‖f (u x + h x) - f (u x) - fderiv ℝ f (u x) (h x)‖ ≤ ε * ‖h x‖).trans
        (mul_le_mul_of_nonneg_left (h.norm_coe_le_norm x) hε.le)

lemma contDiff_nat_superposition (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E → F) (hf : ContDiff ℝ ∞ f), ContDiff ℝ n (superposition (K := K) f hf.continuous) := by
  induction n with
  | zero =>
    intro F _ _ f hf
    exact contDiff_zero.mpr (Differentiable.continuous (fun u => (hasFDerivAt_superposition hf u).differentiableAt))
  | succ n ih =>
    intro F _ _ f hf
    rw [show (↑(n + 1) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun u => continuousMapApplyCLM (superposition (fderiv ℝ f)
      (hf.continuous_fderiv (by simp)) u), ?_, ?_⟩
    · exact (continuousMapApplyCLM (K := K) (E := E) (F := F)).contDiff.comp
        (ih (fderiv ℝ f) (hf.fderiv_right (by simp)))
    · intro u
      exact hasFDerivAt_superposition hf u

theorem contDiff_superposition {f : E → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (superposition (K := K) f hf.continuous) := by
  rw [contDiff_infty]
  exact fun n => contDiff_nat_superposition n f hf


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

theorem smooth_inverse_on {f : X → X} (hf : ContDiff ℝ ∞ f) (x : X)
    (D : X ≃L[ℝ] X) (hd : HasFDerivAt f (D : X →L[ℝ] X) x) :
    ∃ (e : OpenPartialHomeomorph X X) (W : Set X),
      (e : X → X) = f ∧ x ∈ e.source ∧ IsOpen W ∧ f x ∈ W ∧ W ⊆ e.target ∧
      ContDiffOn ℝ ∞ e.symm W := by
  let e := hf.contDiffAt.toOpenPartialHomeomorph f hd (by simp)
  have hex : x ∈ e.source := hf.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hefx : f x ∈ e.target := e.map_source hex
  have hunit : ∀ᶠ z in 𝓝 x, IsUnit (fderiv ℝ f z) := by
    apply (hf.continuous_fderiv (by simp)).continuousAt.eventually
    apply Units.isOpen.mem_nhds
    rw [hd.fderiv]
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr D.bijective
  have hu : ∀ᶠ y in 𝓝 (f x), IsUnit (fderiv ℝ f (e.symm y)) := by
    have hc : Tendsto e.symm (𝓝 (f x)) (𝓝 x) := by
      have hc := e.symm.continuousAt hefx
      change Tendsto e.symm (𝓝 (f x)) (𝓝 (e.symm (f x))) at hc
      have he : e.symm (f x) = x := e.left_inv hex
      rwa [he] at hc
    exact hc.eventually hunit
  obtain ⟨W, hWsub, hWo, hW⟩ := _root_.mem_nhds_iff.mp (hu.and (e.open_target.mem_nhds hefx))
  refine ⟨e, W, rfl, hex, hWo, hW, fun y hy => (hWsub hy).2, ?_⟩
  intro y hy
  obtain ⟨huy, hyt⟩ := hWsub hy
  have hb := ContinuousLinearMap.isUnit_iff_bijective.mp huy
  let A := ContinuousLinearEquiv.ofBijective (fderiv ℝ f (e.symm y))
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have ha : HasFDerivAt (e : X → X) (A : X →L[ℝ] X) (e.symm y) :=
    hf.differentiable (by simp) (e.symm y) |>.hasFDerivAt
  exact (e.contDiffAt_symm hyt ha (hf.contDiffAt)).contDiffWithinAt

end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory intervalIntegral
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology Manifold ContDiff ENNReal NNReal
open Set Filter Function Metric
open scoped Topology ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

abbrev FlowParameters (E : Type u) [TopologicalSpace E] := (ℝ × E) × C(unitInterval, E)

def flowIntegralMap (V : E → E) (hV : Continuous V) (p : FlowParameters E) : FlowParameters E :=
  (p.1, p.2 - ContinuousMap.const unitInterval p.1.2 - p.1.1 • volterra (superposition V hV p.2))

lemma flowIntegralMap_smooth {V : E → E} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (flowIntegralMap V hV.continuous) := by
  refine contDiff_fst.prodMk ((contDiff_snd.sub ?_).sub ?_)
  · exact (ContinuousLinearMap.const ℝ unitInterval : E →L[ℝ] C(unitInterval, E)).contDiff.comp contDiff_fst.snd
  · exact contDiff_fst.fst.smul (volterra.contDiff.comp ((contDiff_superposition hV).comp contDiff_snd))

def flowIntegralDerivative (S : C(unitInterval, E)) : FlowParameters E ≃L[ℝ] FlowParameters E where
  toFun p := (p.1, p.2 - ContinuousMap.const unitInterval p.1.2 - p.1.1 • S)
  invFun p := (p.1, p.2 + ContinuousMap.const unitInterval p.1.2 + p.1.1 • S)
  left_inv p := by ext <;> simp; abel
  right_inv p := by ext <;> simp; abel
  map_add' p q := by ext <;> simp [add_smul]; abel
  map_smul' c p := by ext <;> simp [smul_sub, smul_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma flowIntegralMap_derivative {V : E → E} (hV : ContDiff ℝ ∞ V) (x : E) :
    HasFDerivAt (flowIntegralMap V hV.continuous)
      (flowIntegralDerivative (volterra (superposition V hV.continuous (ContinuousMap.const unitInterval x))) :
        FlowParameters E →L[ℝ] FlowParameters E) ((0,x), ContinuousMap.const unitInterval x) := by
  let p : FlowParameters E := ((0,x), ContinuousMap.const unitInterval x)
  let P := ContinuousLinearMap.fst ℝ (ℝ × E) C(unitInterval, E)
  let U := ContinuousLinearMap.snd ℝ (ℝ × E) C(unitInterval, E)
  let T := (ContinuousLinearMap.fst ℝ ℝ E).comp P
  let X := (ContinuousLinearMap.snd ℝ ℝ E).comp P
  have hQ := volterra.hasFDerivAt.comp p
    (((contDiff_superposition hV).differentiable (by simp) (U p)).hasFDerivAt.comp p U.hasFDerivAt)
  have hh := P.hasFDerivAt (x := p) |>.prodMk
    ((U.hasFDerivAt.sub ((ContinuousLinearMap.const ℝ unitInterval).hasFDerivAt.comp p X.hasFDerivAt)).sub
      (T.hasFDerivAt.smul hQ))
  convert! hh using 1
  ext q s <;> simp [flowIntegralDerivative, p, P, U, T, X]

theorem smooth_integral_paths {V : E → E} (hV : ContDiff ℝ ∞ V) (x : E) :
    ∃ (O : Set (ℝ × E)) (u : (ℝ × E) → C(unitInterval, E)),
      IsOpen O ∧ (0,x) ∈ O ∧ ContDiffOn ℝ ∞ u O ∧ u (0,x) = ContinuousMap.const unitInterval x ∧
      ∀ p ∈ O, u p = ContinuousMap.const unitInterval p.2 + p.1 • volterra (superposition V hV.continuous (u p)) := by
  let p : FlowParameters E := ((0,x), ContinuousMap.const unitInterval x)
  let D := flowIntegralDerivative (volterra (superposition V hV.continuous (ContinuousMap.const unitInterval x)))
  obtain ⟨e, W, hef, hep, hWo, hpW, hWt, hWs⟩ := smooth_inverse_on
    (flowIntegralMap_smooth hV) p D (flowIntegralMap_derivative hV x)
  let z : ℝ × E → FlowParameters E := fun q => (q,0)
  have hzp : z (0,x) = flowIntegralMap V hV.continuous p := by
    simp [z, flowIntegralMap, p]
  refine ⟨z ⁻¹' W, fun q => (e.symm (z q)).2, hWo.preimage (by fun_prop), ?_, ?_, ?_, ?_⟩
  · change z (0,x) ∈ W
    rwa [hzp]
  · exact (hWs.comp (f := z) (s := z ⁻¹' W) (by dsimp [z]; fun_prop) (fun q hq => hq)).snd
  · have he : e.symm (z (0,x)) = p := by
      rw [hzp, ← hef]
      exact e.left_inv hep
    exact congrArg Prod.snd he
  · intro q hq
    have he : flowIntegralMap V hV.continuous (e.symm (z q)) = z q := by
      rw [← hef]
      exact e.right_inv (hWt hq)
    have he1 : (e.symm (z q)).1 = q := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    change (e.symm (z q)).2 - ContinuousMap.const unitInterval (e.symm (z q)).1.2 -
      (e.symm (z q)).1.1 • volterra (superposition V hV.continuous (e.symm (z q)).2) = 0 at he2
    rw [he1] at he2
    simpa only [sub_eq_zero, eq_sub_iff_add_eq, sub_eq_iff_eq_add, add_comm, zero_add] using he2


end YauCounterexamples
end

end OAI
