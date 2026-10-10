import OAI.Analysis.CircleDomains.Rigidity.TraceBalloonRadii
import Mathlib.Topology.Algebra.Order.Field

namespace OAI

/-! Every finite prefix of shrinking balloons is eventually avoided on
an open neighborhood of a point outside the limiting closed disks. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem traceBalloonRadius_le_first {r : ℕ → ℝ} (m j : ℕ) :
    traceBalloonRadius r m j ≤ traceBalloonRadius r 0 j := by
  by_cases hj : 0 < r j
  · have he : traceBalloonRadius r 0 j = 2*r j := by
      norm_num [traceBalloonRadius,hj]
    rw [he]
    exact traceBalloonRadius_le_double m j hj
  · simp only [traceBalloonRadius,ite_eq_right hj,Nat.cast_zero,zero_add,div_one]
    apply div_le_self (traceExtraRadius_pos j).le
    have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith

 theorem exists_finite_balloon_avoidance {c : ℕ → ℂ} {r : ℕ → ℝ}
    (hr : ∀ j, 0 ≤ r j) {z : ℂ} (hz : ∀ j, r j < ‖z-c j‖) (N : ℕ) :
    ∃ (m : ℕ) (V : Set ℂ), IsOpen V ∧ z ∈ V ∧
      ∀ w ∈ V, ∀ j < N, traceBalloonRadius r m j ≤ ‖w-c j‖ := by
  have he (j : ℕ) : ∀ᶠ m in atTop, traceBalloonRadius r m j < ‖z-c j‖ :=
    (traceBalloonRadius_tendsto hr j).eventually (gt_mem_nhds (hz j))
  have hall : ∀ᶠ m in atTop, ∀ j ∈ Finset.range N, traceBalloonRadius r m j < ‖z-c j‖ :=
    (Finset.eventually_all (Finset.range N)).mpr (fun j _ => he j)
  obtain ⟨m,hm⟩ := hall.exists
  let V := ⋂ j ∈ Finset.range N, {w : ℂ | traceBalloonRadius r m j < ‖w-c j‖}
  have hV : IsOpen V := isOpen_biInter_finset (fun j _ => isOpen_lt continuous_const (by fun_prop))
  refine ⟨m,V,hV,mem_iInter₂.mpr hm,?_⟩
  intro w hw j hj
  exact (mem_iInter₂.mp hw j (Finset.mem_range.mpr hj)).le

end CircleDomainRigidity

end

end OAI
