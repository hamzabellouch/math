import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.GaussLemma
import OAI.Geometry.WeakMTW.Coordinates.NormalNeighborhood

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff

namespace RadialCoordinates
noncomputable section

section Fiber
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def fiber (e : OpenPartialHomeomorph (X × Y) (X × Y))
    (he : ∀ q, (e q).1 = q.1) (x : X) : OpenPartialHomeomorph Y Y where
  toFun v := (e (x, v)).2
  invFun y := (e.symm (x, y)).2
  source := {v | (x, v) ∈ e.source}
  target := {y | (x, y) ∈ e.target}
  map_source' := by
    intro v hv
    change (x, (e (x, v)).2) ∈ e.target
    have hp : (x, (e (x, v)).2) = e (x, v) := Prod.ext (he (x, v)).symm rfl
    rw [hp]
    exact e.map_source hv
  map_target' := by
    intro y hy
    have hfst : (e.symm (x, y)).1 = x := by
      rw [← he, e.right_inv hy]
    change (x, (e.symm (x, y)).2) ∈ e.source
    have hp : (x, (e.symm (x, y)).2) = e.symm (x, y) := Prod.ext hfst.symm rfl
    rw [hp]
    exact e.map_target hy
  left_inv' := by
    intro v hv
    have hp : (x, (e (x, v)).2) = e (x, v) := Prod.ext (he (x, v)).symm rfl
    change (e.symm (x, (e (x, v)).2)).2 = v
    rw [hp, e.left_inv hv]
  right_inv' := by
    intro y hy
    have hfst : (e.symm (x, y)).1 = x := by rw [← he, e.right_inv hy]
    have hp : (x, (e.symm (x, y)).2) = e.symm (x, y) := Prod.ext hfst.symm rfl
    change (e (x, (e.symm (x, y)).2)).2 = y
    rw [hp, e.right_inv hy]
  continuousOn_toFun :=
    (e.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv => hv)).snd
  continuousOn_invFun :=
    (e.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hy => hy)).snd
  open_source := e.open_source.preimage (continuous_const.prodMk continuous_id)
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_id)
end Fiber
end
end RadialCoordinates

namespace NormalNeighborhood.NormalFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry NormalNeighborhood

variable {G : E → MetricTensor E} {S : Set E} {x₀ : E}

def normalAt (N : NormalFlow G S x₀) (x : E) : OpenPartialHomeomorph E E :=
  RadialCoordinates.fiber N.normal (fun q => by rw [N.normal_apply]) x

omit [FiniteDimensional ℝ E] in
@[simp] theorem normalAt_apply (N : NormalFlow G S x₀) (x v : E) :
    N.normalAt x v = (N.flow (N.time, (x, v))).1 :=
  congrArg Prod.snd (N.normal_apply (x, v))

omit [FiniteDimensional ℝ E] in
@[simp] theorem normalAt_source (N : NormalFlow G S x₀) (x : E) :
    (N.normalAt x).source = {v | (x, v) ∈ N.normal.source} := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem normalAt_target (N : NormalFlow G S x₀) (x : E) :
    (N.normalAt x).target = {y | (x, y) ∈ N.normal.target} := rfl

omit [FiniteDimensional ℝ E] in
 theorem normalAt_smooth (N : NormalFlow G S x₀) (x : E) :
    ContDiffOn ℝ ∞ (N.normalAt x) (N.normalAt x).source := by
  have hcomp : ContDiffOn ℝ ∞ (fun v => N.flow (N.time, (x, v))) (N.normalAt x).source :=
    N.flow_smooth.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun v hv => N.source_stays (x, v) hv N.time ⟨N.time_pos.le, le_rfl⟩)
  exact hcomp.fst.congr (fun v _ => N.normalAt_apply x v)

omit [FiniteDimensional ℝ E] in
 theorem normalAt_inverse_smooth (N : NormalFlow G S x₀) (x : E) :
    ContDiffOn ℝ ∞ (N.normalAt x).symm (N.normalAt x).target :=
  (N.inverse_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hy => hy)).snd

 theorem normalAt_gauss (N : NormalFlow G S x₀)
    (hS : IsOpen S) (hG : ContDiffOn ℝ ∞ G S)
    (hsym : ∀ z ∈ S, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ S, ∀ v : E, v ≠ 0 → 0 < G z v v)
    {x v : E} (hv : v ∈ (N.normalAt x).source) (w : E) :
    G (N.normalAt x v) (fderiv ℝ (N.normalAt x) v v)
      (fderiv ℝ (N.normalAt x) v w) = N.time ^ 2 * G x v w := by
  have htv := N.source_stays (x, v) hv N.time ⟨N.time_pos.le, le_rfl⟩
  have hdΦ := ((N.flow_smooth _ htv).contDiffAt (N.domain_open.mem_nhds htv)).differentiableAt
    (by simp)
  have hpath : HasFDerivAt (fun v' : E => (N.time, (x, v')))
      ((0 : E →L[ℝ] ℝ).prod ((0 : E →L[ℝ] E).prod (.id ℝ E))) v :=
    (hasFDerivAt_const _ _).prodMk ((hasFDerivAt_const _ _).prodMk (hasFDerivAt_id v))
  have hd := hdΦ.hasFDerivAt.comp v hpath
  have hde : HasFDerivAt (N.normalAt x)
      ((ContinuousLinearMap.fst ℝ E E).comp ((fderiv ℝ N.flow (N.time, (x, v))).comp
        ((0 : E →L[ℝ] ℝ).prod ((0 : E →L[ℝ] E).prod (.id ℝ E))))) v := by
    convert! hd.fst using 1
    ext z
    exact N.normalAt_apply x z
  rw [hde.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]
  change G (N.normalAt x v) (fderiv ℝ N.flow (N.time, (x, v)) (0, (0, v))).1
    (fderiv ℝ N.flow (N.time, (x, v)) (0, (0, w))).1 = _
  rw [normalAt_apply]
  exact GaussLemma.flow_gauss hS hG hsym hpos N.domain_open N.flow_smooth N.initial N.ode
      N.time_pos.le (N.source_stays (x, v) hv) w
end
end NormalNeighborhood.NormalFlow

namespace RadialCoordinates
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
open CoordinateGeometry

omit [FiniteDimensional ℝ E] in
theorem metric_cauchy_sq {B : MetricTensor E}
    (hs : ∀ v w, B v w = B w v) (hp : ∀ v, 0 ≤ B v v) (v w : E) :
    (B v w) ^ 2 ≤ B v v * B w w := by
  have hquad : ∀ t : ℝ, 0 ≤ B v v * (t * t) + (2 * B v w) * t + B w w := by
    intro t
    have h := hp (t • v + w)
    simp only [map_add, map_smul, add_apply,
      smul_apply, smul_eq_mul] at h
    rw [hs w v] at h
    nlinarith only [h]
  have h := discrim_le_zero hquad
  simp only [discrim] at h
  nlinarith only [h]

end
end RadialCoordinates
end

end WeakMTWGlobalSupport

end OAI
