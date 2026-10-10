import OAI.Geometry.SurfaceImmersion.Whitney.LocalCornerBridge
import OAI.Geometry.SurfaceImmersion.Whitney.CornerArcSeparation

namespace OAI

/-! Retaining actual old-branch separation with the constructed corner bridge. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ} {O : Set M}
namespace RegularPathCornerChart

theorem returning_bridge_local_separation (C : RegularPathCornerChart γ t) (hi : Function.Injective γ)
    (hl : StrictAnti C.leftParameter) (hr : StrictMono C.rightParameter)
    (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    ∃ B : LocalCornerBridge γ t O, C.lower < B.left ∧ B.right < C.upper ∧
      ∀ s ∈ Icc B.arc.start B.arc.finish, ∀ u ∈ Ico C.lower B.left ∪ Ioc B.right C.upper,
        B.arc.curve s ≠ γ.extend u := by
  obtain ⟨P,a,b,l,r,hPs,hPf,hb,hLl,hlt,htr,hrU,hPleft,hPright,hPO,hPc,hPL,hPR⟩ :=
    C.returning_corner_arc hi hl hr hO htO
  have hlx : C.leftParameter l = a+b*P.start^2 := by
    have H := (hPc P.start (left_mem_Icc.mpr P.start_lt_finish.le)).2
    rw [hPleft,(C.left_chart l ⟨hLl.le,hlt.le⟩).2] at H
    exact congrFun H 0
  have hrx : C.rightParameter r = a+b*P.finish^2 := by
    have H := (hPc P.finish (right_mem_Icc.mpr P.start_lt_finish.le)).2
    rw [hPright,(C.right_chart r ⟨htr.le,hrU.le⟩).2] at H
    exact congrFun H 0
  let L : ℝ → ℝ := fun s => C.leftParameter.symm (a+b*s^2)
  let R : ℝ → ℝ := fun s => C.rightParameter.symm (a+b*s^2)
  have hLs : ContDiff ℝ ∞ L := C.left_inverse_smooth.comp (by fun_prop)
  have hRs : ContDiff ℝ ∞ R := C.right_inverse_smooth.comp (by fun_prop)
  refine ⟨⟨P,l,r,C.lower_pos.trans hLl,hlt,htr,hrU.trans C.upper_lt_one,
    L,R,hLs,hRs,?_,?_,?_,?_,hPL,hPR,hPO⟩,hLl,hrU,?_⟩
  · change C.leftParameter.symm (a+b*P.start^2) = l
    rw [← hlx,C.leftParameter.symm_apply_apply]
  · change C.rightParameter.symm (a+b*P.finish^2) = r
    rw [← hrx,C.rightParameter.symm_apply_apply]
  · rw [hPs]
    exact returning_left_parameter_deriv_pos C.leftParameter C.left_parameter_smooth
      C.left_inverse_smooth hl a hb
  · rw [hPf]
    exact returning_right_parameter_deriv_pos C.rightParameter C.right_parameter_smooth
      C.right_inverse_smooth hr a hb

  · apply C.returning_arc_local_separation P hl hr hb hlt htr hPs hPf
    · rw [hlx,hPs]
      ring
    · rw [hrx,hPf]
      ring
    · intro s hs
      exact congrFun (hPc s hs).2 0

theorem advancing_bridge_local_separation (C : RegularPathCornerChart γ t)
    (hl : StrictMono C.leftParameter) (hr : StrictMono C.rightParameter)
    (hO : IsOpen O) (htO : γ.extend t ∈ O) :
    ∃ B : LocalCornerBridge γ t O, C.lower < B.left ∧ B.right < C.upper ∧
      ∀ s ∈ Icc B.arc.start B.arc.finish, ∀ u ∈ Ico C.lower B.left ∪ Ioc B.right C.upper,
        B.arc.curve s ≠ γ.extend u := by
  obtain ⟨P,a,b,l,r,hPs,hPf,hb,hLl,hlt,htr,hrU,hPleft,hPright,hPO,hPc,hPL,hPR⟩ :=
    C.advancing_corner_arc hl hr hO htO
  have hlx : C.leftParameter l = a+b*P.start := by
    have H := (hPc P.start (left_mem_Icc.mpr P.start_lt_finish.le)).2
    rw [hPleft,(C.left_chart l ⟨hLl.le,hlt.le⟩).2] at H
    exact congrFun H 0
  have hrx : C.rightParameter r = a+b*P.finish := by
    have H := (hPc P.finish (right_mem_Icc.mpr P.start_lt_finish.le)).2
    rw [hPright,(C.right_chart r ⟨htr.le,hrU.le⟩).2] at H
    exact congrFun H 0
  let L : ℝ → ℝ := fun s => C.leftParameter.symm (a+b*s)
  let R : ℝ → ℝ := fun s => C.rightParameter.symm (a+b*s)
  have hLs : ContDiff ℝ ∞ L := C.left_inverse_smooth.comp (by fun_prop)
  have hRs : ContDiff ℝ ∞ R := C.right_inverse_smooth.comp (by fun_prop)
  refine ⟨⟨P,l,r,C.lower_pos.trans hLl,hlt,htr,hrU.trans C.upper_lt_one,
    L,R,hLs,hRs,?_,?_,?_,?_,hPL,hPR,hPO⟩,hLl,hrU,?_⟩
  · change C.leftParameter.symm (a+b*P.start) = l
    rw [← hlx,C.leftParameter.symm_apply_apply]
  · change C.rightParameter.symm (a+b*P.finish) = r
    rw [← hrx,C.rightParameter.symm_apply_apply]
  · exact advancing_parameter_deriv_pos C.leftParameter C.left_parameter_smooth
      C.left_inverse_smooth hl a hb P.start
  · exact advancing_parameter_deriv_pos C.rightParameter C.right_parameter_smooth
      C.right_inverse_smooth hr a hb P.finish

  · apply C.advancing_arc_local_separation P hl hr hb hlt htr hPs hPf
    · rw [hlx,hPs]
      ring
    · rw [hrx,hPf]
      ring
    · intro s hs
      exact congrFun (hPc s hs).2 0

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
