import OAI.Analysis.CircleDomains.Modulus.NormalizedArgument

namespace OAI

/-! An explicit index for an arc from the unit circle to the origin.
The reference argument at the starting point uses the radial contraction
inside the disk. The resulting real expression is an integer and gains
one under a deck translation. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

def diskInitialArgument (a z : ℂ) : ℝ :=
  circleRepresentative (normalizedArgument a) + Complex.arg (1 - z / a) / (2 * Real.pi)

theorem diskInitialArgument_projects {a z : ℂ} (ha : a ≠ 0) (haz : a ≠ z) :
    (diskInitialArgument a z : UnitAddCircle) = normalizedArgument (a - z) := by
  have he : a * (1 - z / a) = a - z := by field_simp
  have hn : 1 - z / a ≠ 0 := by
    intro h
    apply sub_ne_zero.mpr haz
    rw [← he, h, mul_zero]
  rw [diskInitialArgument, AddCircle.coe_add, coe_circleRepresentative,
    ← normalizedArgument_eq, ← normalizedArgument_mul ha hn, he]

theorem continuousAt_diskInitialArgument {a z : ℂ} (ha : ‖a‖ = 1) (hz : ‖z‖ < 1) :
    ContinuousAt (diskInitialArgument a) z := by
  have hre : 0 < (1 - z / a).re := by
    have hnorm : ‖z / a‖ < 1 := by simpa only [norm_div, ha, div_one] using hz
    have hle := Complex.re_le_norm (z / a)
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  exact continuousAt_const.add
    (((Complex.continuousAt_arg (Or.inl hre)).comp
      (f := fun w : ℂ => 1 - w / a)
      ((continuous_const.sub (continuous_id.div_const a)).continuousAt)).div_const _)

def diskArcIndex (p : AvoidingPathPoint) (θ : ℝ) : ℝ :=
  θ + 1 / 2 - diskInitialArgument (p.val.1 0) p.val.2 - pathArgumentIncrement p - 1

theorem diskArcIndex_integer (p : AvoidingPathPoint) (θ : ℝ)
    (hstart : ‖p.val.1 0‖ = 1) (hend : p.val.1 1 = 0)
    (hθ : (θ : UnitAddCircle) = normalizedArgument p.val.2) :
    ∃ n : ℤ, diskArcIndex p θ = (n : ℝ) := by
  have ha : p.val.1 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hstart
    exact zero_ne_one hstart
  have haz : p.val.1 0 ≠ p.val.2 := fun h => p.property ⟨0, h⟩
  have hz : p.val.2 ≠ 0 := by
    intro h
    exact p.property ⟨1, hend.trans h.symm⟩
  have hp : (diskArcIndex p θ : UnitAddCircle) = 0 := by
    simp only [diskArcIndex, AddCircle.coe_sub, AddCircle.coe_add,
      diskInitialArgument_projects ha haz, pathArgumentIncrement_projects, hθ, hend,
      zero_sub, normalizedArgument_neg hz]
    have hone : ((1 : ℝ) : UnitAddCircle) = 0 := by
      exact (addCircle_eq_iff_exists_int 1 1 0).mpr ⟨1, by norm_num⟩
    rw [hone]
    abel
  obtain ⟨n, hn⟩ := (addCircle_eq_iff_exists_int 1 (diskArcIndex p θ) 0).mp hp
  exact ⟨n, by simpa only [zero_add, mul_one] using hn⟩

theorem diskArcIndex_translate (p : AvoidingPathPoint) (θ : ℝ) (n : ℤ) :
    diskArcIndex p (θ + (n : ℝ)) = diskArcIndex p θ + (n : ℝ) := by
  unfold diskArcIndex
  ring

end CircleDomainRigidity.FiniteTransfer

end

end OAI
