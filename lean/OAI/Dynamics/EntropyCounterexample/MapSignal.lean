import OAI.Dynamics.EntropyCounterexample.Map
import OAI.Dynamics.EntropyCounterexample.PredictionSignal
import OAI.Dynamics.EntropyCounterexample.ClockPrediction

namespace OAI

noncomputable section

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

def scheduledSignal (D : SphereData) (ℓ : Fin 3) (ti tj : ℝ)
    (z : Sphere) (delay : ℕ) : ℂ :=
  (preparationCoeff ti * readoutCoeff ℓ tj / 10) •
    ((D.cutoff z : ℂ) * phase z ^ (2 ^ (delay + 1)))

theorem baseInput_eq_delayed_signal
    (D : SphereData) (ℓ : Fin 3) (ti tj : ℝ) (z : Sphere)
    (i j : ℕ) (hij : i < j)
    (hhit : ∀ m : ℕ, 1 ≤ m →
      readoutCoeff ℓ (predictedClock D m ti z) =
        if m = j - i then readoutCoeff ℓ tj else 0) :
    baseInput D ℓ ti z = D.L ^ (1 + (i : ℤ) - (j : ℤ)) •
      scheduledSignal D ℓ ti tj z (j - i) := by
  have h := prediction_input_eq_delayed_signal D.L (preparationCoeff ti)
    (readoutCoeff ℓ tj) (fun m => readoutCoeff ℓ (predictedClock D m ti z))
    (fun m => (D.cutoff z : ℂ) * phase z ^ (2 ^ (m + 1))) i j hij hhit
  simpa only [baseInput, inputTerm, scheduledSignal, Complex.real_smul,
    Complex.ofReal_mul, mul_assoc, Nat.add_assoc] using h

theorem input_eq_baseInput_of_mem_Ico
    (D : SphereData) (ℓ : Fin 3) {t : ℝ} (ht : t ∈ Set.Ico 0 100) (z : Sphere) :
    input D ℓ (t : AddCircle (100 : ℝ)) z = baseInput D ℓ t z := by
  exact AddCircle.liftIco_zero_coe_apply ht

theorem input_eq_delayed_signal
    (D : SphereData) (ℓ : Fin 3) (ti tj : ℝ) (z : Sphere)
    (hti : ti ∈ Set.Ico 0 100) (i j : ℕ) (hij : i < j)
    (hhit : ∀ m : ℕ, 1 ≤ m →
      readoutCoeff ℓ (predictedClock D m ti z) =
        if m = j - i then readoutCoeff ℓ tj else 0) :
    input D ℓ (ti : AddCircle (100 : ℝ)) z =
      D.L ^ (1 + (i : ℤ) - (j : ℤ)) • scheduledSignal D ℓ ti tj z (j - i) := by
  rw [input_eq_baseInput_of_mem_Ico D ℓ hti z]
  exact baseInput_eq_delayed_signal D ℓ ti tj z i j hij hhit

theorem norm_scheduledSignal_le
    (D : SphereData) (ℓ : Fin 3) (ti tj : ℝ) (z : Sphere) (delay : ℕ)
    (hχ : D.cutoff z ∈ Set.Icc 0 1) :
    ‖scheduledSignal D ℓ ti tj z delay‖ ≤ (1 / 10 : ℝ) := by
  have hα0 := preparationCoeff_nonneg ti
  have hα1 := preparationCoeff_le_one ti
  have hβ0 := readoutCoeff_nonneg ℓ tj
  have hβ1 := readoutCoeff_le_one ℓ tj
  have hc0 : 0 ≤ preparationCoeff ti * readoutCoeff ℓ tj / 10 := by positivity
  have hc1 : preparationCoeff ti * readoutCoeff ℓ tj / 10 ≤ (1 / 10 : ℝ) := by
    have h := mul_le_mul hα1 hβ1 hβ0 (show (0 : ℝ) ≤ 1 by norm_num)
    nlinarith
  have hphase : ‖phase z‖ ^ (2 ^ (delay + 1)) ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (norm_phase_le_one z)
  have hangular : ‖(D.cutoff z : ℂ) * phase z ^ (2 ^ (delay + 1))‖ ≤ 1 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hχ.1]
    exact (mul_le_mul hχ.2 hphase (by positivity) (by norm_num)).trans_eq (by norm_num)
  rw [scheduledSignal, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  exact (mul_le_mul hc1 hangular (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem baseInput_eq_zero_of_not_mem_preparation
    (D : SphereData) (ℓ : Fin 3) {t : ℝ} (ht : t ∉ Set.Ioo 8 12) (z : Sphere) :
    baseInput D ℓ t z = 0 := by
  have hα : preparationCoeff t = 0 := by
    by_contra h
    apply ht
    rwa [← preparationCoeff_support, Function.mem_support]
  simp [baseInput, hα]

theorem input_eq_zero_of_not_mem_preparation
    (D : SphereData) (ℓ : Fin 3) {t : ℝ}
    (ht : t ∈ Set.Ico 0 100) (hprep : t ∉ Set.Ioo 8 12) (z : Sphere) :
    input D ℓ (t : AddCircle (100 : ℝ)) z = 0 := by
  rw [input_eq_baseInput_of_mem_Ico D ℓ ht z]
  exact baseInput_eq_zero_of_not_mem_preparation D ℓ hprep z

theorem norm_phase_coe_eq_one {z : ℂ} (hz : z ≠ 0) :
    ‖phase (z : Sphere)‖ = 1 := by
  simp [phase_coe, Complex.norm_real, norm_ne_zero_iff.mpr hz]

theorem predictedClock_succ_eq_increment (D : SphereData) (n : ℕ) (t : ℝ) (z : Sphere) :
    predictedClock D (n + 1) t z = predictedClock D n t z +
      Clock.increment (predictedClock D n t z)
        (D.gate (((prediction D)^[n] (t, z)).2)) := by
  rw [predictedClock, Function.iterate_succ_apply']
  rfl

theorem predictedClock_monotone_of_gate_nonneg (D : SphereData)
    (hgate : ∀ z, 0 ≤ D.gate z) (t : ℝ) (z : Sphere) :
    Monotone (fun n => predictedClock D n t z) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [predictedClock_succ_eq_increment]
  exact le_add_of_nonneg_right (Clock.increment_nonneg _ (hgate _))

theorem barrier_eq_one_of_readoutCoeff_ne_zero (ℓ : Fin 3) {t : ℝ}
    (ht : readoutCoeff ℓ t ≠ 0) : Clock.barrier t = 1 := by
  have hmem : t ∈ readoutInterval ℓ := by
    rwa [← readoutCoeff_support, Function.mem_support]
  have hbounds := readoutInterval_subset ℓ hmem
  apply Clock.barrier_plateau (by linarith [hbounds.1]) (by linarith [hbounds.2])
  rw [abs_of_nonneg (by linarith [hbounds.1])]
  linarith [hbounds.1]

theorem predictedClock_unit_step_at_readout
    (D : SphereData) (ℓ : Fin 3) (t : ℝ) (z : Sphere) (n : ℕ)
    (hn : readoutCoeff ℓ (predictedClock D n t z) ≠ 0) :
    predictedClock D (n + 1) t z = predictedClock D n t z + 1 := by
  rw [predictedClock_succ_eq_increment,
    Clock.increment_eq_one_of_barrier_eq_one (barrier_eq_one_of_readoutCoeff_ne_zero ℓ hn)]

theorem predicted_readout_single_hit
    (D : SphereData) (hgate : ∀ z, 0 ≤ D.gate z)
    (ℓ : Fin 3) (t : ℝ) (z : Sphere) {d : ℕ}
    (hd : readoutCoeff ℓ (predictedClock D d t z) ≠ 0) (n : ℕ) :
    readoutCoeff ℓ (predictedClock D n t z) =
      if n = d then readoutCoeff ℓ (predictedClock D d t z) else 0 := by
  classical
  by_cases hnd : n = d
  · simp [hnd]
  · rw [ite_eq_right hnd]
    by_contra hn
    apply hnd
    apply clock_readout_unique (predictedClock_monotone_of_gate_nonneg D hgate t z)
      (readoutInterval_length ℓ) ?_
      (predictedClock_unit_step_at_readout D ℓ t z) hn hd
    intro x hx
    change x ∈ readoutInterval ℓ
    rwa [← readoutCoeff_support, Function.mem_support]

theorem input_eq_delayed_signal_of_predicted_hit
    (D : SphereData) (hgate : ∀ z, 0 ≤ D.gate z)
    (ℓ : Fin 3) (ti tj : ℝ) (z : Sphere)
    (hti : ti ∈ Set.Ico 0 100) (i j : ℕ) (hij : i < j)
    (hclock : predictedClock D (j - i) ti z = tj) (hread : readoutCoeff ℓ tj ≠ 0) :
    input D ℓ (ti : AddCircle (100 : ℝ)) z =
      D.L ^ (1 + (i : ℤ) - (j : ℤ)) • scheduledSignal D ℓ ti tj z (j - i) := by
  apply input_eq_delayed_signal D ℓ ti tj z hti i j hij
  intro m _
  have hd : readoutCoeff ℓ (predictedClock D (j - i) ti z) ≠ 0 := by
    rwa [hclock]
  simpa only [hclock] using predicted_readout_single_hit D hgate ℓ ti z hd m

theorem scheduledSignal_eq_readout_smul
    (D : SphereData) (ℓ : Fin 3) (ti tj : ℝ) (z : Sphere) (delay : ℕ) :
    scheduledSignal D ℓ ti tj z delay =
      (readoutCoeff ℓ tj / 10) • ((preparationCoeff ti * D.cutoff z) •
        phase z ^ (2 ^ (delay + 1))) := by
  change (preparationCoeff ti * readoutCoeff ℓ tj / 10) •
    (D.cutoff z • phase z ^ (2 ^ (delay + 1))) = _
  rw [smul_smul, smul_smul]
  congr 1
  ring

theorem sum_scheduledSignal_eq_readout_smul
    (D : SphereData) (ℓ : Fin 3) (t : ℕ → ℝ) (z : ℕ → Sphere)
    (I : Finset ℕ) (j : ℕ) :
    (∑ n ∈ I, scheduledSignal D ℓ (t n) (t j) (z n) (j - n)) =
      (readoutCoeff ℓ (t j) / 10) •
        ∑ n ∈ I, (preparationCoeff (t n) * D.cutoff (z n)) •
          phase (z n) ^ (2 ^ (j - n + 1)) := by
  simp only [scheduledSignal_eq_readout_smul, Finset.smul_sum]

end Problem340.Construction

end

end OAI
