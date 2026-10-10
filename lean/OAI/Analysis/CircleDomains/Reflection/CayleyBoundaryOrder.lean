import OAI.Analysis.CircleDomains.Topology.HalfPlaneDisk
import OAI.Analysis.CircleDomains.Topology.BoundaryClosingArc
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-! The real boundary of the half-plane is sent monotonically to the
positively oriented circle cut at the point at infinity. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def cayleyBoundaryAngle (x : ℝ) : ℝ := unitCircleCut (normalizedArgument (halfPlaneDisk x))

theorem cayleyBoundary_norm (x : ℝ) : ‖halfPlaneDisk x‖ = 1 :=
  halfPlaneDisk_norm_eq (by simp)

theorem cayleyBoundary_ne_one (x : ℝ) : halfPlaneDisk x ≠ 1 :=
  halfPlaneDisk_ne_one (by simp)

theorem continuous_cayleyBoundaryAngle : Continuous cayleyBoundaryAngle := by
  have hM : Continuous (fun x : ℝ => halfPlaneDisk x) :=
    continuousOn_halfPlaneDisk.comp_continuous Complex.continuous_ofReal (by intro x; simp)
  apply continuous_iff_continuousAt.mpr
  intro x
  have hn : halfPlaneDisk (x : ℂ) ≠ 0 := by
    intro he
    have hh := cayleyBoundary_norm x
    rw [he, norm_zero] at hh
    exact zero_ne_one hh
  have hzero : normalizedArgument (halfPlaneDisk x) ≠ (0 : ℝ) := by
    intro he
    apply cayleyBoundary_ne_one x
    rw [← standardCirclePoint_normalizedArgument (cayleyBoundary_norm x), he,
      AddCircle.coe_zero, standardCirclePoint_zero]
  exact continuous_subtype_val.continuousAt.comp
    ((AddCircle.continuousAt_equivIco (1 : ℝ) 0 hzero).comp
      (f := fun y : ℝ => normalizedArgument (halfPlaneDisk y))
      ((continuousAt_normalizedArgument hn).comp (f := fun y : ℝ => halfPlaneDisk y) hM.continuousAt))

theorem cayleyBoundaryAngle_injective : Injective cayleyBoundaryAngle := by
  intro x y he
  have ha := normalizedArgument_injOn_unit_sphere (cayleyBoundary_norm x)
    (cayleyBoundary_norm y) (unitCircleCut_injective he)
  exact Complex.ofReal_injective (halfPlaneDisk_injOn (by simp) (by simp) ha)

theorem cayleyBoundaryAngle_zero : cayleyBoundaryAngle 0 = 1 / 2 := by
  have hM : halfPlaneDisk 0 = -1 := by simp [halfPlaneDisk]
  have hπ : Real.pi / (2 * Real.pi) = 1 / 2 := by field_simp
  unfold cayleyBoundaryAngle
  rw [Complex.ofReal_zero, hM, normalizedArgument_eq, Complex.arg_neg_one, hπ]
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
    (show (1 / 2 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) by constructor <;> norm_num))

theorem cayleyBoundaryAngle_one : cayleyBoundaryAngle 1 = 3 / 4 := by
  have hM : halfPlaneDisk 1 = -Complex.I := by
    unfold halfPlaneDisk
    apply (div_eq_iff (halfPlaneDisk_den_ne_zero (z := 1) (by simp))).mpr
    rw [mul_add]
    simp only [neg_mul, mul_one, Complex.I_mul_I, neg_neg]
    ring
  have hπ : -(Real.pi / 2) / (2 * Real.pi) = -(1 / 4) := by field_simp; ring
  have hc : ((-(1 / 4) : ℝ) : UnitAddCircle) = ((3 / 4 : ℝ) : UnitAddCircle) :=
    (addCircle_eq_iff_exists_int 1 _ _).mpr ⟨-1, by norm_num⟩
  unfold cayleyBoundaryAngle
  rw [Complex.ofReal_one, hM, normalizedArgument_eq, Complex.arg_neg_I, hπ, hc]
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
    (show (3 / 4 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) by constructor <;> norm_num))

theorem strictMono_cayleyBoundaryAngle : StrictMono cayleyBoundaryAngle := by
  rcases continuous_cayleyBoundaryAngle.strictMono_of_inj cayleyBoundaryAngle_injective with h | h
  · exact h
  · have hh := h (show (0 : ℝ) < 1 by norm_num)
    rw [cayleyBoundaryAngle_zero, cayleyBoundaryAngle_one] at hh
    norm_num at hh

theorem cayleyBoundary_mem_closingArc (a x : ℝ) :
    halfPlaneDisk x ∈ range (boundaryClosingArc (halfPlaneDisk a) (cayleyBoundary_norm a)) ↔ x ≤ a := by
  let A := cayleyBoundaryAngle a
  have hA : 0 < A := boundary_angle_pos (cayleyBoundary_norm a) (cayleyBoundary_ne_one a)
  constructor
  · rintro ⟨t, ht⟩
    have hc := congrArg normalizedArgument ht
    change normalizedArgument (standardCirclePoint ((A * (t : ℝ) : ℝ) : UnitAddCircle)) =
      normalizedArgument (halfPlaneDisk x) at hc
    rw [normalizedArgument_standardCirclePoint] at hc
    have hb := boundary_arc_parameter_mem (cayleyBoundary_norm a) (cayleyBoundary_ne_one a) t
    change A * (t : ℝ) ∈ Ico (0 : ℝ) 1 at hb
    have hqx : cayleyBoundaryAngle x = A * (t : ℝ) := by
      unfold cayleyBoundaryAngle unitCircleCut
      rw [← hc]
      exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
        (show A * (t : ℝ) ∈ Ico (0 : ℝ) (0 + 1) by simpa only [zero_add] using hb))
    apply strictMono_cayleyBoundaryAngle.le_iff_le.mp
    rw [hqx]
    exact mul_le_of_le_one_right hA.le t.property.2
  · intro hxa
    have hqx : cayleyBoundaryAngle x ≤ A := strictMono_cayleyBoundaryAngle.monotone hxa
    let t : PathTime := ⟨cayleyBoundaryAngle x / A,
      div_nonneg (unitCircleCut_mem _).1 hA.le, (div_le_one hA).mpr hqx⟩
    refine ⟨t, ?_⟩
    change standardCirclePoint ((A * (cayleyBoundaryAngle x / A) : ℝ) : UnitAddCircle) = _
    rw [mul_div_cancel₀ _ hA.ne']
    change standardCirclePoint ((unitCircleCut (normalizedArgument (halfPlaneDisk x)) : ℝ) : UnitAddCircle) = _
    rw [show ((unitCircleCut (normalizedArgument (halfPlaneDisk x)) : ℝ) : UnitAddCircle) =
      normalizedArgument (halfPlaneDisk x) from AddCircle.coe_equivIco]
    exact standardCirclePoint_normalizedArgument (cayleyBoundary_norm x)

end CircleDomainRigidity

end

end OAI
