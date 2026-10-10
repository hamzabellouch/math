import OAI.Dynamics.EntropyCounterexample.Definitions

namespace OAI

noncomputable section

namespace Problem340.SphereCutoffs

def clockGateAmbient (x : SphereAmbient) : ℝ :=
  Real.smoothTransition ((25 * x 2 + 15) / 8)

def preparationCutoffAmbient (x : SphereAmbient) : ℝ :=
  Real.smoothTransition (5 * x 2 + 4) *
    Real.smoothTransition (1 - 2 * x 2)

def clockGate (x : StandardSphere2) : ℝ := clockGateAmbient x.1

def preparationCutoff (x : StandardSphere2) : ℝ := preparationCutoffAmbient x.1

@[fun_prop]
theorem contDiff_clockGateAmbient {n : ℕ∞} : ContDiff ℝ n clockGateAmbient := by
  have hh : ContDiff ℝ n (fun x : SphereAmbient => x 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff
  exact Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul hh).add contDiff_const).div_const 8)

@[fun_prop]
theorem contDiff_preparationCutoffAmbient {n : ℕ∞} :
    ContDiff ℝ n preparationCutoffAmbient := by
  have hh : ContDiff ℝ n (fun x : SphereAmbient => x 2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).contDiff
  exact (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul hh).add contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp
      (contDiff_const.sub (contDiff_const.mul hh)))

@[continuity, fun_prop]
theorem continuous_clockGate : Continuous clockGate :=
  (@contDiff_clockGateAmbient 0).continuous.comp continuous_subtype_val

@[continuity, fun_prop]
theorem continuous_preparationCutoff : Continuous preparationCutoff :=
  (@contDiff_preparationCutoffAmbient 0).continuous.comp continuous_subtype_val

theorem clockGateAmbient_nonneg (x : SphereAmbient) : 0 ≤ clockGateAmbient x :=
  Real.smoothTransition.nonneg _

theorem clockGateAmbient_le_one (x : SphereAmbient) : clockGateAmbient x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem preparationCutoffAmbient_nonneg (x : SphereAmbient) :
    0 ≤ preparationCutoffAmbient x :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem preparationCutoffAmbient_le_one (x : SphereAmbient) :
    preparationCutoffAmbient x ≤ 1 := by
  exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)

theorem clockGateAmbient_eq_zero {x : SphereAmbient} (h : x 2 ≤ -3 / 5) :
    clockGateAmbient x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem clockGateAmbient_eq_one {x : SphereAmbient} (h : -7 / 25 ≤ x 2) :
    clockGateAmbient x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem preparationCutoffAmbient_eq_one {x : SphereAmbient}
    (hlo : -3 / 5 ≤ x 2) (hhi : x 2 ≤ 0) : preparationCutoffAmbient x = 1 := by
  unfold preparationCutoffAmbient
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 5 * x 2 + 4),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 1 - 2 * x 2)]
  norm_num

theorem preparationCutoffAmbient_eq_zero_of_low {x : SphereAmbient}
    (h : x 2 ≤ -4 / 5) : preparationCutoffAmbient x = 0 := by
  unfold preparationCutoffAmbient
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 * x 2 + 4 ≤ 0), zero_mul]

theorem preparationCutoffAmbient_eq_zero_of_high {x : SphereAmbient}
    (h : 1 / 2 ≤ x 2) : preparationCutoffAmbient x = 0 := by
  unfold preparationCutoffAmbient
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 1 - 2 * x 2 ≤ 0), mul_zero]

theorem support_preparationCutoffAmbient :
    Function.support preparationCutoffAmbient ⊆
      {x : SphereAmbient | -4 / 5 < x 2 ∧ x 2 < 1 / 2} := by
  intro x hx
  constructor
  · by_contra h
    exact hx (preparationCutoffAmbient_eq_zero_of_low (le_of_not_gt h))
  · by_contra h
    exact hx (preparationCutoffAmbient_eq_zero_of_high (le_of_not_gt h))

theorem clockGate_mem_Icc (x : StandardSphere2) : clockGate x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨clockGateAmbient_nonneg x.1, clockGateAmbient_le_one x.1⟩

theorem preparationCutoff_mem_Icc (x : StandardSphere2) :
    preparationCutoff x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨preparationCutoffAmbient_nonneg x.1, preparationCutoffAmbient_le_one x.1⟩

theorem clockGate_eq_zero_of_radius {x : StandardSphere2} {r : ℝ}
    (hr : 0 ≤ r) (hsmall : r ≤ 1 / 2)
    (hheight : x.1 2 = (r ^ 2 - 1) / (r ^ 2 + 1)) : clockGate x = 0 := by
  apply clockGateAmbient_eq_zero
  rw [hheight]
  apply (div_le_iff₀ (by positivity : 0 < r ^ 2 + 1)).2
  nlinarith [mul_self_le_mul_self hr hsmall]

theorem clockGate_eq_one_of_radius {x : StandardSphere2} {r : ℝ}
    (hlarge : 3 / 4 ≤ r)
    (hheight : x.1 2 = (r ^ 2 - 1) / (r ^ 2 + 1)) : clockGate x = 1 := by
  apply clockGateAmbient_eq_one
  rw [hheight]
  apply (le_div_iff₀ (by positivity : 0 < r ^ 2 + 1)).2
  nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 3 / 4) hlarge]

theorem preparationCutoff_eq_one_of_radius {x : StandardSphere2} {r : ℝ}
    (hlo : 1 / 2 ≤ r) (hhi : r ≤ 1)
    (hheight : x.1 2 = (r ^ 2 - 1) / (r ^ 2 + 1)) :
    preparationCutoff x = 1 := by
  apply preparationCutoffAmbient_eq_one
  · rw [hheight]
    apply (le_div_iff₀ (by positivity : 0 < r ^ 2 + 1)).2
    nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2) hlo]
  · rw [hheight]
    apply (div_le_iff₀ (by positivity : 0 < r ^ 2 + 1)).2
    nlinarith [mul_self_le_mul_self (by linarith : 0 ≤ r) hhi]

theorem preparationCutoff_eq_zero_of_small_radius {x : StandardSphere2} {r : ℝ}
    (hr : 0 ≤ r) (hsmall : r ≤ 1 / 3)
    (hheight : x.1 2 = (r ^ 2 - 1) / (r ^ 2 + 1)) :
    preparationCutoff x = 0 := by
  apply preparationCutoffAmbient_eq_zero_of_low
  rw [hheight]
  apply (div_le_iff₀ (by positivity : 0 < r ^ 2 + 1)).2
  nlinarith [mul_self_le_mul_self hr hsmall]

theorem preparationCutoff_eq_zero_of_large_radius {x : StandardSphere2} {r : ℝ}
    (hlarge : 3 ≤ r ^ 2)
    (hheight : x.1 2 = (r ^ 2 - 1) / (r ^ 2 + 1)) :
    preparationCutoff x = 0 := by
  apply preparationCutoffAmbient_eq_zero_of_high
  rw [hheight]
  apply (le_div_iff₀ (by positivity : 0 < r ^ 2 + 1)).2
  linarith

end Problem340.SphereCutoffs

end

end OAI
