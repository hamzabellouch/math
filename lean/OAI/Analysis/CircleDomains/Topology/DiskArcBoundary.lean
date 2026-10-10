import OAI.Analysis.CircleDomains.Topology.DiskArcIndexLocal

namespace OAI

/-! The explicit index on the boundary of the disk is the floor of the
lifted angle minus the starting angle. This supplies its orientation and
the positive unit boundary period. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

lemma re_one_sub_pos_of_norm_le {w : ℂ} (hw : ‖w‖ ≤ 1) (hne : w ≠ 1) :
    0 < (1 - w).re := by
  have hle : w.re ≤ 1 := (Complex.re_le_norm w).trans hw
  have hlt : w.re < 1 := by
    by_contra hn
    have hr : w.re = 1 := le_antisymm hle (not_lt.mp hn)
    have hn : ‖w‖ = 1 := le_antisymm hw (hr ▸ Complex.re_le_norm w)
    have hi : w.im = 0 := Complex.abs_re_eq_norm.mp (by rw [hr, hn, abs_one])
    exact hne (Complex.ext (by simpa using hr) (by simpa using hi))
  simpa only [Complex.sub_re, Complex.one_re, sub_pos] using hlt

lemma re_one_sub_div_pos {w z : ℂ} (hw : ‖w‖ ≤ 1) (hz : ‖z‖ = 1) (hne : w ≠ z) :
    0 < (1 - w / z).re := by
  apply re_one_sub_pos_of_norm_le
  · simpa only [norm_div, hz, div_one] using hw
  · intro he
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz
      exact zero_ne_one hz
    exact hne ((div_eq_one_iff_eq hz0).mp he)

lemma abs_argument_turns_lt_quarter {w : ℂ} (hw : 0 < w.re) :
    |Complex.arg w / (2 * Real.pi)| < 1 / 4 := by
  have hp : 0 < 2 * Real.pi := by positivity
  rw [abs_div, abs_of_pos hp, div_lt_iff₀ hp]
  have h := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  linarith

theorem boundary_pathArgumentIncrement (p : AvoidingPathPoint)
    (hz : ‖p.val.2‖ = 1) (hend : p.val.1 1 = 0)
    (hclosed : ∀ t, ‖p.val.1 t‖ ≤ 1) :
    pathArgumentIncrement p = -Complex.arg (1 - p.val.1 0 / p.val.2) / (2 * Real.pi) := by
  have hz0 : p.val.2 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact zero_ne_one hz
  have hpos (t : PathTime) : 0 < (1 - p.val.1 t / p.val.2).re :=
    re_one_sub_div_pos (hclosed t) hz (fun h => p.property ⟨t, h⟩)
  let u : C(unitInterval, ℝ) :=
    ⟨fun t => circleRepresentative (normalizedArgument (-p.val.2)) +
      Complex.arg (1 - p.val.1 t / p.val.2) / (2 * Real.pi), by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact continuousAt_const.add
        (((Complex.continuousAt_arg (Or.inl (hpos t))).comp
          (f := fun t => 1 - p.val.1 t / p.val.2)
          ((continuous_const.sub (p.val.1.continuous.div_const p.val.2)).continuousAt)).div_const _)⟩
  have hproj (t : unitInterval) : (u t : UnitAddCircle) = pathArgument p t := by
    change ((circleRepresentative (normalizedArgument (-p.val.2)) +
      Complex.arg (1 - p.val.1 t / p.val.2) / (2 * Real.pi) : ℝ) : UnitAddCircle) = _
    rw [AddCircle.coe_add, coe_circleRepresentative, ← normalizedArgument_eq,
      ← normalizedArgument_mul (neg_ne_zero.mpr hz0)
        (ne_of_apply_ne Complex.re (ne_of_gt (hpos t)))]
    congr 1
    change -p.val.2 * (1 - p.val.1 t / p.val.2) = p.val.1 t - p.val.2
    field_simp
    ring
  rw [pathArgumentIncrement, circlePathIncrement_eq_lift _ u hproj]
  simp only [u, ContinuousMap.coe_mk, hend, zero_div, sub_zero, Complex.arg_one, zero_div,
    add_zero]
  ring

theorem diskArcIndex_boundary_floor (p : AvoidingPathPoint) (θ : ℝ)
    (hstart : ‖p.val.1 0‖ = 1) (hz : ‖p.val.2‖ = 1) (hend : p.val.1 1 = 0)
    (hclosed : ∀ t, ‖p.val.1 t‖ ≤ 1)
    (hθ : (θ : UnitAddCircle) = normalizedArgument p.val.2) :
    diskArcIndex p θ = (⌊θ - circleRepresentative (normalizedArgument (p.val.1 0))⌋ : ℤ) := by
  obtain ⟨n, hn⟩ := diskArcIndex_integer p θ hstart hend hθ
  have hne : p.val.1 0 ≠ p.val.2 := fun h => p.property ⟨0, h⟩
  have hα := abs_argument_turns_lt_quarter (re_one_sub_div_pos hz.le hstart hne.symm)
  have hβ := abs_argument_turns_lt_quarter (re_one_sub_div_pos hstart.le hz hne)
  have hi := boundary_pathArgumentIncrement p hz hend hclosed
  have hform : diskArcIndex p θ =
      θ - circleRepresentative (normalizedArgument (p.val.1 0)) - 1 / 2 -
        Complex.arg (1 - p.val.2 / p.val.1 0) / (2 * Real.pi) +
        Complex.arg (1 - p.val.1 0 / p.val.2) / (2 * Real.pi) := by
    rw [diskArcIndex, diskInitialArgument, hi]
    ring
  have hn' : ⌊θ - circleRepresentative (normalizedArgument (p.val.1 0))⌋ = n :=
    Int.floor_eq_iff.mpr ⟨by linarith [(abs_lt.mp hα).1, (abs_lt.mp hβ).2],
      by linarith [(abs_lt.mp hα).2, (abs_lt.mp hβ).1]⟩
  rw [hn, hn']

end CircleDomainRigidity.FiniteTransfer

end

end OAI
