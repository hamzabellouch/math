import OAI.Combinatorics.ContingencyTables.Transport.FiniteIndependentAverages

namespace OAI

/-! # Independent finite experiments with an explicitly bounded mean bias -/

namespace ContingencyTables.FiniteIndependentAverages

open CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section

variable {X : Type*} [Fintype X] [Nonempty X]

theorem sampleAverage_absolute_failure (g : X → ℝ) (N : ℕ) (hN : 0 < N)
    (r : ℝ) (hr : 0 < r) :
    uniformAverage (fun xs : Fin N → X =>
      if r < |sampleAverage g N xs-uniformAverage g| then (1:ℝ) else 0) ≤
      uniformAverage (fun x => (g x-uniformAverage g)^2)/(N*r^2) := by
  have hp (xs : Fin N → X) :
      (if r < |sampleAverage g N xs-uniformAverage g| then (1:ℝ) else 0) ≤
        (sampleAverage g N xs-uniformAverage g)^2/r^2 := by
    split_ifs with h
    · rw [le_div_iff₀ (sq_pos_of_pos hr)]
      simpa only [one_mul,sq_abs] using
        (sq_le_sq₀ hr.le (abs_nonneg _)).mpr h.le
    · positivity
  calc
    _ ≤ uniformAverage (fun xs : Fin N → X =>
        (sampleAverage g N xs-uniformAverage g)^2/r^2) := uniformAverage_mono _ _ hp
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [uniformAverage_mul_const,sampleAverage_secondMoment g N hN]
      ring

lemma bounded_variance (g : X → ℝ) (U : ℝ)
    (hg : ∀ x,0 ≤ g x ∧ g x ≤ U) :
    uniformAverage (fun x => (g x-uniformAverage g)^2) ≤ U^2 := by
  have hm := mean_bounds g 0 U hg
  have hU : 0 ≤ U := hm.1.trans hm.2
  have hp (x : X) : (g x-uniformAverage g)^2 ≤ U^2 := by
    have habs : |g x-uniformAverage g| ≤ U := abs_le.mpr ⟨by linarith [(hg x).1],by linarith [(hg x).2]⟩
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hU).mpr habs
  simpa only [uniformAverage_const] using uniformAverage_mono _ (fun _ : X => U^2) hp

/-- The target is an exact mathematical mean; the experiment's own mean
may differ, but only by the displayed deterministic bias. -/
theorem biased_target_failure (g : X → ℝ) (U target delta : ℝ)
    (hg : ∀ x,0 ≤ g x ∧ g x ≤ U) (htarget : 0 < target) (hdelta : 0 < delta)
    (hbias : |uniformAverage g-target| ≤ delta*target/2)
    (N : ℕ) (hN : 0 < N) :
    uniformAverage (fun xs : Fin N → X =>
      if delta*target < |sampleAverage g N xs-target| then (1:ℝ) else 0) ≤
      4*U^2/(N*(delta*target)^2) := by
  have hr : 0 < delta*target/2 := by positivity
  have hp (xs : Fin N → X) :
      (if delta*target < |sampleAverage g N xs-target| then (1:ℝ) else 0) ≤
        if delta*target/2 < |sampleAverage g N xs-uniformAverage g| then 1 else 0 := by
    split_ifs with h h'
    · rfl
    · exfalso
      have hh : |sampleAverage g N xs-target| ≤
          |sampleAverage g N xs-uniformAverage g|+|uniformAverage g-target| := by
        simpa only [sub_add_sub_cancel] using abs_add_le
          (sampleAverage g N xs-uniformAverage g) (uniformAverage g-target)
      have hn := le_of_not_gt h'
      linarith
    · norm_num
    · rfl
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ uniformAverage (fun xs : Fin N → X =>
        if delta*target/2 < |sampleAverage g N xs-uniformAverage g| then (1:ℝ) else 0) :=
      uniformAverage_mono _ _ hp
    _ ≤ uniformAverage (fun x => (g x-uniformAverage g)^2)/(N*(delta*target/2)^2) :=
      sampleAverage_absolute_failure g N hN _ hr
    _ ≤ U^2/(N*(delta*target/2)^2) :=
      div_le_div_of_nonneg_right (bounded_variance g U hg) (by positivity)
    _ = _ := by
      field_simp [hNR.ne',hdelta.ne',htarget.ne']; ring

end

end ContingencyTables.FiniteIndependentAverages

end OAI
