import Mathlib

namespace OAI

/-! Smooth positive-mass bumps on the unit circle, localized inside one period. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.LoopDensity

def circleBump (φ : ContDiffBump (0 : ℝ)) (c t : ℝ) : ℝ :=
  φ (Real.sin (Real.pi * (t - c)))

lemma circleBump_smooth (φ : ContDiffBump (0 : ℝ)) (c : ℝ) :
    ContDiff ℝ ∞ (circleBump φ c) :=
  φ.contDiff.comp ((contDiff_const.mul (contDiff_id.sub contDiff_const)).sin)

lemma circleBump_periodic (φ : ContDiffBump (0 : ℝ)) (c : ℝ) :
    Function.Periodic (circleBump φ c) 1 := by
  intro t
  unfold circleBump
  rw [show Real.pi * (t + 1 - c) = Real.pi * (t - c) + Real.pi by ring]
  rw [Real.sin_add_pi, φ.neg]

lemma circleBump_at_center (φ : ContDiffBump (0 : ℝ)) (c : ℝ) : circleBump φ c c = 1 := by
  simp only [circleBump, sub_self, mul_zero, Real.sin_zero]
  exact φ.one_of_mem_closedBall (mem_closedBall_self φ.rIn_pos.le)

private lemma sine_nonzero {c t : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hne : t ≠ c) : Real.sin (Real.pi * (t - c)) ≠ 0 := by
  rw [ne_eq, Real.sin_eq_zero_iff_of_lt_of_lt]
  · exact mul_ne_zero Real.pi_ne_zero (sub_ne_zero.mpr hne)
  · have h : -1 < t - c := by linarith [hc.2, ht.1]
    simpa using mul_lt_mul_of_pos_left h Real.pi_pos
  · have h : t - c < 1 := by linarith [hc.1, ht.2]
    simpa using mul_lt_mul_of_pos_left h Real.pi_pos

/-- An actual smooth periodic nonnegative density of mass one supported in any
prescribed neighborhood of an interior point of the fundamental interval. -/
theorem exists_localized_bump {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    {V : Set ℝ} (hV : IsOpen V) (hcV : c ∈ V) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ Function.Periodic ψ 1 ∧
      (∀ t, 0 ≤ ψ t) ∧ (∫ t in 0..1, ψ t) = 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, t ∉ V → ψ t = 0 := by
  let K := Icc (0 : ℝ) 1 \ V
  have hK : IsCompact K := isCompact_Icc.diff hV
  have hf : Continuous (fun t : ℝ => |Real.sin (Real.pi * (t - c))|) := by fun_prop
  have hr : ∃ r : ℝ, 0 < r ∧ ∀ t ∈ K, r ≤ |Real.sin (Real.pi * (t - c))| := by
    by_cases hne : K.Nonempty
    · obtain ⟨t, ht, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
      refine ⟨|Real.sin (Real.pi * (t - c))|, abs_pos.mpr ?_, hmin⟩
      apply sine_nonzero hc ht.1
      intro heq
      exact ht.2 (heq ▸ hcV)
    · exact ⟨1, zero_lt_one, fun t ht => (hne ⟨t, ht⟩).elim⟩
  obtain ⟨r, hr, hbound⟩ := hr
  let φ : ContDiffBump (0 : ℝ) := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let f := circleBump φ c
  have hfs : ContDiff ℝ ∞ f := circleBump_smooth φ c
  have hfn (t : ℝ) : 0 ≤ f t := φ.nonneg
  have hfc : f c = 1 := circleBump_at_center φ c
  have hfi : 0 < ∫ t in 0..1, f t :=
    intervalIntegral.integral_pos zero_lt_one hfs.continuous.continuousOn
      (fun t _ => hfn t) ⟨c, ⟨hc.1.le, hc.2.le⟩, by rw [hfc]; norm_num⟩
  let ψ : ℝ → ℝ := fun t => f t / ∫ s in 0..1, f s
  refine ⟨ψ, hfs.div_const _, ?_, ?_, ?_, ?_⟩
  · intro t
    change f (t + 1) / _ = f t / _
    exact congrArg (fun x : ℝ => x / ∫ s in 0..1, f s) (circleBump_periodic φ c t)
  · intro t
    exact div_nonneg (hfn t) hfi.le
  · change (∫ t in 0..1, f t / _) = 1
    rw [intervalIntegral.integral_div, div_self hfi.ne']
  · intro t ht htV
    have hz : f t = 0 := by
      apply φ.zero_of_le_dist
      change r / 2 ≤ dist (Real.sin (Real.pi * (t - c))) 0
      rw [Real.dist_eq, sub_zero]
      exact (by linarith : r / 2 ≤ r).trans (hbound t ⟨ht, htV⟩)
    change f t / _ = 0
    rw [hz, zero_div]

end ClosedSurfaceR4.LoopDensity

end

end OAI
