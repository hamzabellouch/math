import OAI.Geometry.ComplexBundle.Projection
import Mathlib.Topology.VectorBundle.Basic

namespace OAI

noncomputable section

/-! The projection line bundle and its dual. -/

section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Topology Bundle
namespace Kaplansky
variable {d : ℕ}

def projectionLineTransition (i j : Fin d) (p : projectionSpace d 1) : ℂ :=
  inner ℂ (unitProjectionColumn p j) (unitProjectionColumn p i)

theorem projectionLineTransition_self (i : Fin d) (p : projectionSpace d 1)
    (hi : p ∈ projectionChartSet i) : projectionLineTransition i i p = 1 := by
  rw [projectionLineTransition, inner_self_eq_norm_sq_to_K, unitProjectionColumn_norm p i hi]
  simp

theorem projectionLineTransition_comp (i j k : Fin d) (p : projectionSpace d 1)
    (hj : p ∈ projectionChartSet j) :
    projectionLineTransition j k p * projectionLineTransition i j p = projectionLineTransition i k p := by
  have he := congrArg (inner ℂ (unitProjectionColumn p k))
    (unitProjectionColumn_reconstruct p j hj (unitProjectionColumn p i) (unitProjectionColumn_mem p i))
  simpa only [projectionLineTransition, inner_smul_right, mul_comm] using he

theorem projectionLineTransition_star (i j : Fin d) (p : projectionSpace d 1) :
    star (projectionLineTransition i j p) = projectionLineTransition j i p :=
  inner_conj_symm _ _

theorem projectionLineTransition_unitary (i j : Fin d) (p : projectionSpace d 1)
    (hi : p ∈ projectionChartSet i) (hj : p ∈ projectionChartSet j) :
    star (projectionLineTransition i j p) * projectionLineTransition i j p = 1 := by
  rw [projectionLineTransition_star, projectionLineTransition_comp i j i p hj,
    projectionLineTransition_self i p hi]

theorem continuousOn_projectionLineTransition (i j : Fin d) :
    ContinuousOn (projectionLineTransition i j) (projectionChartSet i ∩ projectionChartSet j) :=
  ((continuousOn_unitProjectionColumn j).mono Set.inter_subset_right).inner
    ((continuousOn_unitProjectionColumn i).mono Set.inter_subset_left)

/-- A genuine complex line-bundle core on the compact space of orthogonal
rank-one projections. Its transition functions are constructed, not assumed. -/
def projectionLineCore (d : ℕ) : VectorBundleCore ℂ (projectionSpace d 1) ℂ (Fin d) where
  baseSet := projectionChartSet
  isOpen_baseSet := isOpen_projectionChartSet
  indexAt p := (exists_projectionColumn_ne_zero p).choose
  mem_baseSet_at p := (exists_projectionColumn_ne_zero p).choose_spec
  coordChange i j p := projectionLineTransition i j p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p hp z := by simp [projectionLineTransition_self i p hp]
  continuousOn_coordChange i j := (continuousOn_projectionLineTransition i j).smul continuousOn_const
  coordChange_comp i j k p hp z := by
    change projectionLineTransition j k p * (projectionLineTransition i j p * z) =
      projectionLineTransition i k p * z
    rw [← mul_assoc, projectionLineTransition_comp i j k p hp.1.2]

/-- Identify each constructed fiber with the actual projected line in
Euclidean space. -/
def projectionLineFiberEquiv (p : projectionSpace d 1) :
    (projectionLineCore d).Fiber p ≃ₗ[ℂ] projectionLine p where
  toFun z := ⟨(show ℂ from z) • unitProjectionColumn p ((projectionLineCore d).indexAt p),
    (projectionLine p).smul_mem (show ℂ from z) (unitProjectionColumn_mem p _)⟩
  invFun v := inner ℂ (unitProjectionColumn p ((projectionLineCore d).indexAt p)) v.val
  left_inv z := by
    change ℂ at z
    change inner ℂ (unitProjectionColumn p _) ((show ℂ from z) • unitProjectionColumn p _) = (show ℂ from z)
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K,
      unitProjectionColumn_norm p _ ((projectionLineCore d).mem_baseSet_at p)]
    simp
  right_inv v := Subtype.ext (unitProjectionColumn_reconstruct p _
    ((projectionLineCore d).mem_baseSet_at p) v.val v.property)
  map_add' z w := by apply Subtype.ext; exact add_smul _ _ _
  map_smul' z w := by apply Subtype.ext; exact mul_smul _ _ _

theorem projectionLine_realization_chart (p : projectionSpace d 1)
    (z : (projectionLineCore d).Fiber p) (i : Fin d) (hi : p ∈ projectionChartSet i) :
    (projectionLineFiberEquiv p z).val =
      ((projectionLineCore d).localTriv i ⟨p,z⟩).2 • unitProjectionColumn p i := by
  change (show ℂ from z) • unitProjectionColumn p ((projectionLineCore d).indexAt p) =
    (projectionLineTransition ((projectionLineCore d).indexAt p) i p * (show ℂ from z)) • unitProjectionColumn p i
  rw [mul_comm, mul_smul, projectionLineTransition,
    unitProjectionColumn_reconstruct p i hi _ (unitProjectionColumn_mem p _)]

abbrev ProjectionLineTotal (d : ℕ) :=
  {z : projectionSpace d 1 × EuclideanSpace ℂ (Fin d) // z.2 ∈ projectionLine z.1}

def projectionLineRealization (z : TotalSpace ℂ (projectionLineCore d).Fiber) :
    EuclideanSpace ℂ (Fin d) := (projectionLineFiberEquiv z.proj z.2).val

theorem continuous_projectionLineRealization :
    Continuous (projectionLineRealization (d := d)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let L := projectionLineCore d
  let i := L.indexAt z.proj
  have hi : z.proj ∈ projectionChartSet i := L.mem_baseSet_at z.proj
  have hp : Continuous (π ℂ L.Fiber) := FiberBundle.continuous_proj ℂ L.Fiber
  have hx : z ∈ (L.localTriv i).source := (L.localTriv i).mem_source.mpr hi
  have hc := ((L.localTriv i).continuousAt hx).snd
  have hv := ((continuousOn_unitProjectionColumn i z.proj hi).continuousAt
    ((isOpen_projectionChartSet i).mem_nhds hi)).comp hp.continuousAt
  apply (hc.smul hv).congr_of_eventuallyEq
  filter_upwards [hp.continuousAt ((isOpen_projectionChartSet i).mem_nhds hi)] with w hw
  exact projectionLine_realization_chart w.proj w.2 i hw

def projectionLineToTotal (z : TotalSpace ℂ (projectionLineCore d).Fiber) : ProjectionLineTotal d :=
  ⟨(z.proj,projectionLineRealization z),(projectionLineFiberEquiv z.proj z.2).property⟩

def projectionLineFromTotal (z : ProjectionLineTotal d) : TotalSpace ℂ (projectionLineCore d).Fiber :=
  ⟨z.val.1, (projectionLineFiberEquiv z.val.1).symm ⟨z.val.2,z.property⟩⟩

theorem projectionLineFromTotal_chart (z : ProjectionLineTotal d) (i : Fin d) :
    ((projectionLineCore d).localTriv i (projectionLineFromTotal z)).2 =
      inner ℂ (unitProjectionColumn z.val.1 i) z.val.2 := by
  let p := z.val.1
  let j := (projectionLineCore d).indexAt p
  change projectionLineTransition j i p * inner ℂ (unitProjectionColumn p j) z.val.2 = _
  have he := congrArg (inner ℂ (unitProjectionColumn p i))
    (unitProjectionColumn_reconstruct p j ((projectionLineCore d).mem_baseSet_at p) z.val.2 z.property)
  simpa only [projectionLineTransition, inner_smul_right, mul_comm] using he

theorem continuous_projectionLineFromTotal : Continuous (projectionLineFromTotal (d := d)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  rw [FiberBundle.continuousAt_totalSpace]
  have hp : Continuous (fun z : ProjectionLineTotal d => z.val.1) := continuous_subtype_val.fst
  refine ⟨hp.continuousAt, ?_⟩
  let i := (projectionLineCore d).indexAt z.val.1
  have hi : z.val.1 ∈ projectionChartSet i := (projectionLineCore d).mem_baseSet_at z.val.1
  have hu : ContinuousAt (fun w : ProjectionLineTotal d => unitProjectionColumn w.val.1 i) z :=
    Filter.Tendsto.comp (g := fun p : projectionSpace d 1 => unitProjectionColumn p i)
      (f := fun w : ProjectionLineTotal d => w.val.1)
      ((continuousOn_unitProjectionColumn i z.val.1 hi).continuousAt
        ((isOpen_projectionChartSet i).mem_nhds hi)) hp.continuousAt
  have hc : ContinuousAt (fun w : ProjectionLineTotal d =>
      inner ℂ (unitProjectionColumn w.val.1 i) w.val.2) z :=
    hu.inner (continuous_subtype_val.snd.continuousAt (x := z))
  exact hc.congr (Filter.Eventually.of_forall (fun w => (projectionLineFromTotal_chart w i).symm))

/-- The constructed line bundle is homeomorphic to the actual incidence
subspace of the compact projection base times Euclidean space. -/
def projectionLineTotalHomeomorph (d : ℕ) :
    TotalSpace ℂ (projectionLineCore d).Fiber ≃ₜ ProjectionLineTotal d where
  toFun := projectionLineToTotal
  invFun := projectionLineFromTotal
  left_inv z := by
    rcases z with ⟨p,v⟩
    change (⟨p,(projectionLineFiberEquiv p).symm (projectionLineFiberEquiv p v)⟩ :
      TotalSpace ℂ (projectionLineCore d).Fiber) = ⟨p,v⟩
    rw [LinearEquiv.symm_apply_apply]
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val ((projectionLineFiberEquiv z.val.1).apply_symm_apply ⟨z.val.2,z.property⟩)
  continuous_toFun := (FiberBundle.continuous_proj ℂ (projectionLineCore d).Fiber).prodMk
    continuous_projectionLineRealization |>.subtype_mk _
  continuous_invFun := continuous_projectionLineFromTotal

end Kaplansky

end

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix Topology Bundle
namespace Kaplansky
variable {d : ℕ}

/-- The dual (hyperplane) line core, with inverse unitary transitions. -/
def projectionDualLineCore (d : ℕ) : VectorBundleCore ℂ (projectionSpace d 1) ℂ (Fin d) where
  baseSet := projectionChartSet
  isOpen_baseSet := isOpen_projectionChartSet
  indexAt := (projectionLineCore d).indexAt
  mem_baseSet_at := (projectionLineCore d).mem_baseSet_at
  coordChange i j p := star (projectionLineTransition i j p) • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p hp z := by simp [projectionLineTransition_self i p hp]
  continuousOn_coordChange i j := (continuousOn_projectionLineTransition i j).star.smul continuousOn_const
  coordChange_comp i j k p hp z := by
    change star (projectionLineTransition j k p) * (star (projectionLineTransition i j p) * z) =
      star (projectionLineTransition i k p) * z
    rw [← mul_assoc, ← star_mul, mul_comm (projectionLineTransition i j p),
      projectionLineTransition_comp i j k p hp.1.2]

/-- The constructed dual fiber is the full algebraic dual of the actual line. -/
def projectionDualLineFiberEquiv (p : projectionSpace d 1) :
    (projectionDualLineCore d).Fiber p ≃ₗ[ℂ] (projectionLine p →ₗ[ℂ] ℂ) where
  toFun z := (show ℂ from z) • (projectionLineFiberEquiv p).symm.toLinearMap
  invFun f := f (projectionLineFiberEquiv p (show (projectionLineCore d).Fiber p from (1 : ℂ)))
  left_inv z := by
    change ℂ at z
    let e : ℂ ≃ₗ[ℂ] projectionLine p := projectionLineFiberEquiv p
    change z * e.symm (e 1) = z
    rw [LinearEquiv.symm_apply_apply, mul_one]
  right_inv f := by
    let e : ℂ ≃ₗ[ℂ] projectionLine p := projectionLineFiberEquiv p
    apply LinearMap.ext
    intro v
    change f (e 1) * e.symm v = f v
    have hv : v = e.symm v • e 1 := by
      rw [← map_smul]
      simp
    conv_rhs => rw [hv, map_smul]
    exact mul_comm _ _
  map_add' _ _ := add_smul _ _ _
  map_smul' _ _ := mul_smul _ _ _

/-- Evaluation of the dual on the line is independent of the local chart. -/
theorem projectionDualLine_pairing_chart (p : projectionSpace d 1)
    (z : (projectionDualLineCore d).Fiber p) (w : (projectionLineCore d).Fiber p)
    (i : Fin d) (hi : p ∈ projectionChartSet i) :
    ((projectionDualLineCore d).localTriv i ⟨p,z⟩).2 *
      ((projectionLineCore d).localTriv i ⟨p,w⟩).2 = (show ℂ from z) * (show ℂ from w) := by
  let j := (projectionLineCore d).indexAt p
  change (star (projectionLineTransition j i p) * (show ℂ from z)) *
    (projectionLineTransition j i p * (show ℂ from w)) = _
  calc
    _ = (star (projectionLineTransition j i p) * projectionLineTransition j i p) *
      ((show ℂ from z) * (show ℂ from w)) := by ring
    _ = _ := by rw [projectionLineTransition_unitary j i p ((projectionLineCore d).mem_baseSet_at p) hi, one_mul]

end Kaplansky

end

end OAI
