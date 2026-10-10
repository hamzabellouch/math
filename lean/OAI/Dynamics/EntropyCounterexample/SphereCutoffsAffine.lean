import OAI.Dynamics.EntropyCounterexample.SphereCutoffs

namespace OAI

noncomputable section

open Filter Topology

namespace Problem340.SphereCutoffs

def affineHeight (z : ℂ) : ℝ := (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1)

def affineClockGate (z : ℂ) : ℝ :=
  Real.smoothTransition ((25 * affineHeight z + 15) / 8)

def affinePreparationCutoff (z : ℂ) : ℝ :=
  Real.smoothTransition (5 * affineHeight z + 4) *
    Real.smoothTransition (1 - 2 * affineHeight z)

@[fun_prop]
theorem contDiff_affineHeight {n : ℕ∞} : ContDiff ℝ n affineHeight := by
  exact ((contDiff_norm_sq ℝ).sub contDiff_const).div
    ((contDiff_norm_sq ℝ).add contDiff_const) (fun z => by positivity)

@[fun_prop]
theorem contDiff_affineClockGate {n : ℕ∞} : ContDiff ℝ n affineClockGate := by
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul contDiff_affineHeight).add contDiff_const).div_const 8)

@[fun_prop]
theorem contDiff_affinePreparationCutoff {n : ℕ∞} :
    ContDiff ℝ n affinePreparationCutoff := by
  exact (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_affineHeight).add contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp
      (contDiff_const.sub (contDiff_const.mul contDiff_affineHeight)))

theorem affineClockGate_mem_Icc (z : ℂ) : affineClockGate z ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem affinePreparationCutoff_mem_Icc (z : ℂ) :
    affinePreparationCutoff z ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)⟩

theorem affineClockGate_eq_zero {z : ℂ} (h : ‖z‖ ≤ 1 / 2) :
    affineClockGate z = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : affineHeight z ≤ -3 / 5 := by
    apply (div_le_iff₀ (by positivity : 0 < ‖z‖ ^ 2 + 1)).2
    nlinarith [mul_self_le_mul_self (norm_nonneg z) h]
  linarith

theorem affineClockGate_eq_one {z : ℂ} (h : 3 / 4 ≤ ‖z‖) :
    affineClockGate z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hh : -7 / 25 ≤ affineHeight z := by
    apply (le_div_iff₀ (by positivity : 0 < ‖z‖ ^ 2 + 1)).2
    nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 3 / 4) h]
  linarith

theorem affinePreparationCutoff_eq_one {z : ℂ}
    (hlo : 1 / 2 ≤ ‖z‖) (hhi : ‖z‖ ≤ 1) : affinePreparationCutoff z = 1 := by
  have hl : -3 / 5 ≤ affineHeight z := by
    apply (le_div_iff₀ (by positivity : 0 < ‖z‖ ^ 2 + 1)).2
    nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hlo]
  have hh : affineHeight z ≤ 0 := by
    apply (div_le_iff₀ (by positivity : 0 < ‖z‖ ^ 2 + 1)).2
    nlinarith [mul_self_le_mul_self (norm_nonneg z) hhi]
  unfold affinePreparationCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 5 * affineHeight z + 4),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 1 - 2 * affineHeight z)]
  norm_num

theorem affinePreparationCutoff_eq_zero_of_small {z : ℂ} (h : ‖z‖ ≤ 1 / 3) :
    affinePreparationCutoff z = 0 := by
  have hh : affineHeight z ≤ -4 / 5 := by
    apply (div_le_iff₀ (by positivity : 0 < ‖z‖ ^ 2 + 1)).2
    nlinarith [mul_self_le_mul_self (norm_nonneg z) h]
  unfold affinePreparationCutoff
  rw [Real.smoothTransition.zero_of_nonpos
    (by linarith : 5 * affineHeight z + 4 ≤ 0), zero_mul]

theorem affinePreparationCutoff_eq_zero_of_large {z : ℂ} (h : 3 ≤ ‖z‖ ^ 2) :
    affinePreparationCutoff z = 0 := by
  have hh : 1 / 2 ≤ affineHeight z := by
    apply (le_div_iff₀ (by positivity : 0 < ‖z‖ ^ 2 + 1)).2
    linarith
  unfold affinePreparationCutoff
  rw [Real.smoothTransition.zero_of_nonpos
    (by linarith : 1 - 2 * affineHeight z ≤ 0), mul_zero]

theorem clockGate_eq_affineClockGate {x : StandardSphere2} {z : ℂ}
    (hh : x.1 2 = affineHeight z) : clockGate x = affineClockGate z := by
  simp only [clockGate, clockGateAmbient, affineClockGate, hh]

theorem preparationCutoff_eq_affinePreparationCutoff {x : StandardSphere2} {z : ℂ}
    (hh : x.1 2 = affineHeight z) :
    preparationCutoff x = affinePreparationCutoff z := by
  simp only [preparationCutoff, preparationCutoffAmbient, affinePreparationCutoff, hh]

theorem hasCompactSupport_affinePreparationCutoff :
    HasCompactSupport affinePreparationCutoff := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 2)
  intro z hz
  have hz' : 2 < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  apply affinePreparationCutoff_eq_zero_of_large
  nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) hz'.le]

theorem continuous_onePointElim_of_eq_const_off_isCompact
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (c : Y) (hf : Continuous f) {K : Set X}
    (hK : IsCompact K) (hclosed : IsClosed K)
    (hout : ∀ x ∉ K, f x = c) :
    Continuous (fun z : OnePoint X => z.elim c f) := by
  apply (OnePoint.continuous_iff _).2
  refine ⟨?_, hf⟩
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [hK.compl_mem_coclosedCompact_of_isClosed hclosed] with x hx
  exact (hout x hx).symm

def onePointClockGate (z : OnePoint ℂ) : ℝ := z.elim 1 affineClockGate

def onePointPreparationCutoff (z : OnePoint ℂ) : ℝ := z.elim 0 affinePreparationCutoff

@[simp] theorem onePointClockGate_coe (z : ℂ) :
    onePointClockGate (z : OnePoint ℂ) = affineClockGate z := rfl

@[simp] theorem onePointClockGate_infty : onePointClockGate OnePoint.infty = 1 := rfl

@[simp] theorem onePointPreparationCutoff_coe (z : ℂ) :
    onePointPreparationCutoff (z : OnePoint ℂ) = affinePreparationCutoff z := rfl

@[simp] theorem onePointPreparationCutoff_infty :
    onePointPreparationCutoff OnePoint.infty = 0 := rfl

@[continuity, fun_prop]
theorem continuous_onePointClockGate : Continuous onePointClockGate := by
  apply continuous_onePointElim_of_eq_const_off_isCompact _ _
    (@contDiff_affineClockGate 0).continuous (isCompact_closedBall (0 : ℂ) 1)
    Metric.isClosed_closedBall
  intro z hz
  have hz' : 1 < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  exact affineClockGate_eq_one (by linarith)

@[continuity, fun_prop]
theorem continuous_onePointPreparationCutoff : Continuous onePointPreparationCutoff := by
  apply continuous_onePointElim_of_eq_const_off_isCompact _ _
    (@contDiff_affinePreparationCutoff 0).continuous (isCompact_closedBall (0 : ℂ) 2)
    Metric.isClosed_closedBall
  intro z hz
  have hz' : 2 < ‖z‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
  apply affinePreparationCutoff_eq_zero_of_large
  nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 2) hz'.le]

theorem onePointClockGate_mem_Icc (z : OnePoint ℂ) :
    onePointClockGate z ∈ Set.Icc (0 : ℝ) 1 := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => exact affineClockGate_mem_Icc z

theorem onePointPreparationCutoff_mem_Icc (z : OnePoint ℂ) :
    onePointPreparationCutoff z ∈ Set.Icc (0 : ℝ) 1 := by
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => exact affinePreparationCutoff_mem_Icc z

end Problem340.SphereCutoffs

end

end OAI
