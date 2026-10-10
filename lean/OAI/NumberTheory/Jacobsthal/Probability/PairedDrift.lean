import OAI.NumberTheory.Jacobsthal.Paths.PairedHitting

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.PairedDrift

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures KernelDensityBridge
open RegenerationDrift CompactExponentialMoments PairedHitting

noncomputable def V (s : OddState) : ℝ := Real.exp s.1

theorem V_pos (s : OddState) : 0 < V s := Real.exp_pos _
theorem V_one_le (s : OddState) : 1 ≤ V s := Real.one_le_exp_iff.mpr (by linarith [s.2])
theorem V_measurable : Measurable V := Real.measurable_exp.comp measurable_subtype_coe

theorem paired_drift : ∃ a C : ℝ, 0 < a ∧ a < 1 ∧ 0 < C ∧ ∀ s : OddState,
    (∫⁻ t, ENNReal.ofReal (V t) ∂pairedOdd s) ≤ ENNReal.ofReal a * ENNReal.ofReal (V s) + ENNReal.ofReal C := by
  obtain ⟨C, hC, he, ho⟩ := kernel_global_drift
  have hκ := driftFactor_pos
  have hκ1 := driftFactor_lt_one
  have he' : ∀ s : EvenState, (∫⁻ t : OddState, ENNReal.ofReal (Real.exp t.1) ∂evenToOdd s) ≤
      ENNReal.ofReal driftFactor * ENNReal.ofReal (Real.exp s.1) + ENNReal.ofReal C := by
    intro s
    rw [evenToOdd_lintegral_ratio s (H := fun x : ℝ => ENNReal.ofReal (Real.exp x)) (ENNReal.measurable_ofReal.comp Real.measurable_exp)]
    have h := ENNReal.ofReal_le_ofReal (he s).2
    rw [ofReal_integral_eq_lintegral_ofReal (he s).1 (Eventually.of_forall (fun t => (Real.exp_pos t).le)),
      ENNReal.ofReal_add (mul_pos hκ (Real.exp_pos _)).le hC.le, ENNReal.ofReal_mul hκ.le] at h
    exact h
  have ho' : ∀ s : OddState, (∫⁻ t : EvenState, ENNReal.ofReal (Real.exp t.1) ∂oddToEven s) ≤
      ENNReal.ofReal driftFactor * ENNReal.ofReal (Real.exp s.1) + ENNReal.ofReal C := by
    intro s
    rw [oddToEven_lintegral_ratio s (H := fun x : ℝ => ENNReal.ofReal (Real.exp x)) (ENNReal.measurable_ofReal.comp Real.measurable_exp)]
    have h := ENNReal.ofReal_le_ofReal (ho s).2
    rw [ofReal_integral_eq_lintegral_ofReal (ho s).1 (Eventually.of_forall (fun t => (Real.exp_pos t).le)),
      ENNReal.ofReal_add (mul_pos hκ (Real.exp_pos _)).le hC.le, ENNReal.ofReal_mul hκ.le] at h
    exact h
  refine ⟨driftFactor ^ 2, (1 + driftFactor) * C, sq_pos_of_pos hκ, by nlinarith,
    mul_pos (by linarith) hC, ?_⟩
  intro s
  rw [pairedOdd, Kernel.lintegral_comp evenToOdd oddToEven s (g := fun t : OddState => ENNReal.ofReal (V t)) (ENNReal.measurable_ofReal.comp V_measurable)]
  change (∫⁻ t : EvenState, ∫⁻ u : OddState, ENNReal.ofReal (Real.exp u.1) ∂evenToOdd t ∂oddToEven s) ≤ _
  have hEV : Measurable (fun t : EvenState => ENNReal.ofReal (Real.exp t.1)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_subtype_coe)
  calc
    _ ≤ ∫⁻ t : EvenState, ENNReal.ofReal driftFactor * ENNReal.ofReal (Real.exp t.1) + ENNReal.ofReal C ∂oddToEven s :=
      lintegral_mono he'
    _ = ENNReal.ofReal driftFactor * (∫⁻ t : EvenState, ENNReal.ofReal (Real.exp t.1) ∂oddToEven s) + ENNReal.ofReal C := by
      rw [lintegral_add_left (f := fun t : EvenState => ENNReal.ofReal driftFactor * ENNReal.ofReal (Real.exp t.1)) (measurable_const.mul hEV) (fun _ => ENNReal.ofReal C), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp
    _ ≤ ENNReal.ofReal driftFactor * (ENNReal.ofReal driftFactor * ENNReal.ofReal (Real.exp s.1) + ENNReal.ofReal C) + ENNReal.ofReal C :=
      add_le_add (mul_le_mul le_rfl (ho' s) zero_le zero_le) le_rfl
    _ = _ := by
      rw [ENNReal.ofReal_pow hκ.le, ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + driftFactor),
        ENNReal.ofReal_add zero_le_one hκ.le, ENNReal.ofReal_one]
      dsimp [V]
      ring

theorem pairedKilled_drift : ∃ a C : ℝ, 0 < a ∧ a < 1 ∧ 0 < C ∧ ∀ s : OddState,
    (∫⁻ t, ENNReal.ofReal (V t) ∂pairedKilled s) ≤ ENNReal.ofReal a * ENNReal.ofReal (V s) + ENNReal.ofReal C := by
  obtain ⟨a, C, ha, ha1, hC, hb⟩ := paired_drift
  refine ⟨a, C, ha, ha1, hC, ?_⟩
  intro s
  rw [pairedKilled, Kernel.lintegral_restrict]
  exact le_trans (setLIntegral_le_lintegral _ _) (hb s)

theorem pairedKilled_iterated_drift : ∃ a B : ℝ, 0 < a ∧ a < 1 ∧ 0 < B ∧
    ∀ n : ℕ, ∀ s : OddState,
      (∫⁻ t, ENNReal.ofReal (V t) ∂(pairedKilled ^ n) s) ≤
        ENNReal.ofReal (a ^ n * V s + B) := by
  obtain ⟨a, C, ha, ha1, hC, hOne⟩ := pairedKilled_drift
  let B := C / (1 - a)
  have hB : 0 < B := div_pos hC (by linarith)
  have hBE : a * B + C = B := by dsimp [B]; field_simp [show 1 - a ≠ 0 by linarith]; ring
  have hEE : ENNReal.ofReal a * ENNReal.ofReal B + ENNReal.ofReal C = ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_add (mul_pos ha hB).le hC.le, hBE]
  have hV : Measurable (fun s : OddState => ENNReal.ofReal (V s)) := ENNReal.measurable_ofReal.comp V_measurable
  have hIter : ∀ n : ℕ, ∀ s : OddState,
      (∫⁻ t, ENNReal.ofReal (V t) ∂(pairedKilled ^ n) s) ≤
        (ENNReal.ofReal a) ^ n * ENNReal.ofReal (V s) + ENNReal.ofReal B := by
    intro n
    induction n with
    | zero =>
      intro s
      change (∫⁻ t, ENNReal.ofReal (V t) ∂Measure.dirac s) ≤ _
      rw [lintegral_dirac' s hV]
      simp only [pow_zero, one_mul]
      exact le_add_of_nonneg_right zero_le
    | succ n ih =>
      intro s
      have hp : pairedKilled ^ (n + 1) = pairedKilled ∘ₖ (pairedKilled ^ n) := pow_succ' pairedKilled n
      rw [hp, Kernel.lintegral_comp _ _ _ hV]
      calc
        _ ≤ ∫⁻ t, ENNReal.ofReal a * ENNReal.ofReal (V t) + ENNReal.ofReal C ∂(pairedKilled ^ n) s :=
          lintegral_mono hOne
        _ = ENNReal.ofReal a * (∫⁻ t, ENNReal.ofReal (V t) ∂(pairedKilled ^ n) s) +
            ENNReal.ofReal C * (pairedKilled ^ n) s univ := by
          rw [lintegral_add_left (f := fun t : OddState => ENNReal.ofReal a * ENNReal.ofReal (V t)) (measurable_const.mul hV) (fun _ => ENNReal.ofReal C), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const]
        _ ≤ ENNReal.ofReal a * ((ENNReal.ofReal a) ^ n * ENNReal.ofReal (V s) + ENNReal.ofReal B) + ENNReal.ofReal C := by
          apply add_le_add
          · exact mul_le_mul le_rfl (ih s) zero_le zero_le
          · simpa only [mul_one] using mul_le_mul (le_refl (ENNReal.ofReal C)) (paired_survival_le_one n s) zero_le zero_le
        _ = _ := by rw [mul_add, add_assoc, hEE, pow_succ]; ring
  refine ⟨a, B, ha, ha1, hB, ?_⟩
  intro n s
  rw [ENNReal.ofReal_add (mul_nonneg (pow_nonneg ha.le _) (V_pos s).le) hB.le,
    ENNReal.ofReal_mul (pow_nonneg ha.le _), ENNReal.ofReal_pow ha.le]
  exact hIter n s

theorem block_drift_algebra {a B p v e mass : ℝ} (ha : a ≤ 1 / 4) (hB : 0 ≤ B)
    (hp : 0 < p) (hp1 : p ≤ 1) (hv : 0 ≤ v) (he : e ≤ a * v + B) (hm : mass ≤ 1)
    (hcase : mass ≤ 1 - p ∨ 8 * B ≤ v) :
    e + (2 * B / p) * mass ≤ (1 - p / 2) * (v + 2 * B / p) := by
  let D := 2 * B / p
  have hD : 0 ≤ D := div_nonneg (by linarith) hp.le
  have hpD : p * D = 2 * B := by dsimp [D]; field_simp
  have hav : a * v ≤ v / 4 := by nlinarith [mul_le_mul_of_nonneg_right ha hv]
  have hrv : v / 2 ≤ (1 - p / 2) * v := by
    nlinarith [mul_le_mul_of_nonneg_right (show (1 : ℝ) / 2 ≤ 1 - p / 2 by linarith) hv]
  change e + D * mass ≤ (1 - p / 2) * (v + D)
  rcases hcase with hsmall | hlarge
  · have hmD := mul_le_mul_of_nonneg_left hsmall hD
    nlinarith
  · have hmD := mul_le_mul_of_nonneg_left hm hD
    nlinarith

end NumberTheoryLean.PairedDrift

end

end Erdos970

end OAI
