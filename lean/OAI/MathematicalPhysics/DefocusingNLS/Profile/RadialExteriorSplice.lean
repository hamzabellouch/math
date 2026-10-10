import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialSpliceDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorPropagator
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace OAI

/-! Joining the finite continuation to the original nonlinear exterior tail. -/

open Set Filter Topology
namespace DefocusingNLS

noncomputable def radialExteriorSplice (S : ℝ) (X Y : ℝ → ℂ × ℂ) (t : ℝ) : ℂ × ℂ :=
  if t ≤ S then X t else Y t

theorem radialExteriorSplice_continuous (S : ℝ) (X Y : ℝ → ℂ × ℂ)
    (hX : Continuous X) (hY : Continuous Y) (he : X S=Y S) :
    Continuous (radialExteriorSplice S X Y) := by
  apply hX.if_le hY continuous_id continuous_const
  intro t ht
  change t=S at ht
  subst t
  exact he

theorem radialExteriorSplice_hasDerivAt (S t : ℝ) (X Y : ℝ → ℂ × ℂ)
    (V : ℝ → (ℂ × ℂ) → ℂ × ℂ)
    (hX : t ≤ S → HasDerivAt X (V t (X t)) t)
    (hY : S ≤ t → HasDerivAt Y (V t (Y t)) t)
    (hmatch : X S=Y S) :
    HasDerivAt (radialExteriorSplice S X Y) (V t (radialExteriorSplice S X Y t)) t := by
  rcases lt_trichotomy t S with h | h | h
  · simp only [radialExteriorSplice,ite_eq_left h.le]
    apply (hX h.le).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds h] with r hr
    exact ite_eq_left hr.le
  · subst t
    have hl : HasDerivWithinAt (radialExteriorSplice S X Y) (V S (X S)) (Iic S) S := by
      apply (hX le_rfl).hasDerivWithinAt.congr
      · intro r hr
        exact ite_eq_left hr
      · exact ite_eq_left le_rfl
    have hr : HasDerivWithinAt (radialExteriorSplice S X Y) (V S (X S)) (Ici S) S := by
      rw [hmatch]
      apply (hY le_rfl).hasDerivWithinAt.congr
      · intro r hr
        change S ≤ r at hr
        rcases hr.eq_or_lt with rfl | h
        · simpa only [radialExteriorSplice,ite_eq_left le_rfl] using hmatch
        · exact ite_eq_right h.not_ge
      · simpa only [radialExteriorSplice,ite_eq_left le_rfl] using hmatch
    have hd := hl.union hr
    rw [Iic_union_Ici] at hd
    simpa only [radialExteriorSplice,ite_eq_left le_rfl] using hd.hasDerivAt (by simp)
  · simp only [radialExteriorSplice,ite_eq_right h.not_ge]
    apply (hY h.le).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds h] with r hr
    exact ite_eq_right hr.not_ge

theorem radialExteriorSplice_uniform_limit (L S : ℝ)
    (X Y : ℕ → ℝ → ℂ × ℂ) (g : ℝ → ℂ × ℂ)
    (hX : TendstoUniformlyOn X g atTop (Icc L S))
    (hY : TendstoUniformlyOn Y g atTop (Ici S)) :
    TendstoUniformlyOn (fun n => radialExteriorSplice S (X n) (Y n)) g atTop (Ici L) := by
  rw [Metric.tendstoUniformlyOn_iff] at hX hY ⊢
  intro ε hε
  filter_upwards [hX ε hε,hY ε hε] with n hnX hnY t ht
  by_cases h : t ≤ S
  · simpa only [radialExteriorSplice,ite_eq_left h] using hnX t ⟨ht,h⟩
  · simpa only [radialExteriorSplice,ite_eq_right h] using hnY t (not_le.mp h).le

end DefocusingNLS

end OAI
