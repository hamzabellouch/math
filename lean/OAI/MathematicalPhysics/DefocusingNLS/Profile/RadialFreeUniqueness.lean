import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeComponents

namespace OAI

/-! Uniqueness of the actual short-shell complex integral solution. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_free_integral_unique (b l u : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hl : (3 : ℝ) ≤ l)
    (hu : u ≤ (10/3 : ℝ)) (hlu : l ≤ u) (hwidth : u-l ≤ (1/1000 : ℝ))
    (X Y : ℝ → ℂ × ℂ) (hX : Continuous X) (hY : Continuous Y)
    (hXE : ∀ r ∈ Icc l u, X r=(1,0)+∫ t in l..r, radialFreeField b t (X t))
    (hYE : ∀ r ∈ Icc l u, Y r=(1,0)+∫ t in l..r, radialFreeField b t (Y t)) :
    EqOn X Y (Icc l u) := by
  obtain ⟨m,hm,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hlu)
    (hX.sub hY).norm.continuousOn
  let M := ‖X m-Y m‖
  have hM : 0 ≤ M := norm_nonneg _
  have hInt (Z : ℝ → ℂ × ℂ) (hZ : Continuous Z) :
      IntervalIntegrable (fun t => radialFreeField b t (Z t)) volume l m :=
    ContinuousOn.intervalIntegrable_of_Icc hm.1
      ((radialFreeField_continuousOn_curve b l u (by linarith) Z hZ).mono
        (fun t ht => ⟨ht.1,ht.2.trans hm.2⟩))
  have hEq : X m-Y m=∫ t in l..m, radialFreeField b t (X t-Y t) := by
    rw [hXE m hm,hYE m hm,add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (hInt X hX) (hInt Y hY)]
    apply intervalIntegral.integral_congr
    intro t _
    exact (radialFreeField_sub b t (X t) (Y t)).symm
  have hBound : M ≤ 7*M*(m-l) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => by
      have htI : t ∈ Icc l m := ⟨(uIoc_of_le hm.1 ▸ ht).1.le,(uIoc_of_le hm.1 ▸ ht).2⟩
      have htU : t ∈ Icc l u := ⟨htI.1,htI.2.trans hm.2⟩
      exact (radialFreeField_norm b t hb ⟨hl.trans htU.1,htU.2.trans hu⟩ (X t-Y t)).trans
        (mul_le_mul_of_nonneg_left (hmax htU) (by norm_num)))
    calc
      M = ‖∫ t in l..m, radialFreeField b t (X t-Y t)‖ := congrArg norm hEq
      _ ≤ 7*M*(m-l) := by
        simpa only [abs_of_nonneg (sub_nonneg.mpr hm.1),M,Pi.sub_apply] using hh
  have hM0 : M=0 := by
    have hlen : m-l ≤ (1/1000 : ℝ) := by linarith [hm.2]
    have hprod := mul_le_mul_of_nonneg_left hlen (show 0 ≤ 7*M by positivity)
    nlinarith
  intro r hr
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  exact le_antisymm ((hmax hr).trans_eq hM0) (norm_nonneg _)

end DefocusingNLS

end OAI
