import OAI.Dynamics.EntropyCounterexample.Map
import OAI.Dynamics.EntropyCounterexample.ClockPrediction

namespace OAI

noncomputable section

namespace Problem340.Construction

@[simp] theorem predictedClock_zero (D : SphereData) (t : ℝ) (z : Sphere) :
    predictedClock D 0 t z = t := rfl

theorem predictedClock_succ (D : SphereData) (n : ℕ) (t : ℝ) (z : Sphere) :
    predictedClock D (n + 1) t z = predictedClock D n t z +
      Clock.increment (predictedClock D n t z) (D.gate (((prediction D)^[n] (t, z)).2)) := by
  simp only [predictedClock, Function.iterate_succ_apply', prediction]

theorem predictedClock_step_bounds (D : SphereData)
    (hgate0 : ∀ z, 0 ≤ D.gate z) (hgate1 : ∀ z, D.gate z ≤ 1)
    (n : ℕ) (t : ℝ) (z : Sphere) :
    0 ≤ predictedClock D (n + 1) t z - predictedClock D n t z ∧
      predictedClock D (n + 1) t z - predictedClock D n t z ≤ 1 := by
  rw [predictedClock_succ]
  constructor
  · linarith [Clock.increment_nonneg (predictedClock D n t z)
      (hgate0 (((prediction D)^[n] (t, z)).2))]
  · linarith [Clock.increment_le_one (predictedClock D n t z)
      (hgate1 (((prediction D)^[n] (t, z)).2))]

theorem predictedClock_monotone (D : SphereData)
    (hgate0 : ∀ z, 0 ≤ D.gate z) (t : ℝ) (z : Sphere) :
    Monotone (fun n => predictedClock D n t z) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [predictedClock_succ]
  exact le_add_of_nonneg_right (Clock.increment_nonneg _ (hgate0 _))

theorem predictedClock_unit_step (D : SphereData) (n : ℕ) (t : ℝ) (z : Sphere)
    (hlo : 70 ≤ predictedClock D n t z) (hhi : predictedClock D n t z ≤ 82) :
    predictedClock D (n + 1) t z = predictedClock D n t z + 1 := by
  rw [predictedClock_succ]
  have hb : Clock.barrier (predictedClock D n t z) = 1 := by
    apply Clock.barrier_plateau (by linarith) (by linarith)
    rw [abs_of_nonneg (by linarith : 0 ≤ predictedClock D n t z - 50)]
    linarith
  rw [Clock.increment_eq_one_of_barrier_eq_one hb]

theorem readoutCoeff_mem_interval (i : Fin 3) {t : ℝ} (h : readoutCoeff i t ≠ 0) :
    t ∈ readoutInterval i := by
  rw [← readoutCoeff_support]
  exact h

theorem predictedClock_readout_unique (D : SphereData)
    (hgate0 : ∀ z, 0 ≤ D.gate z) (i : Fin 3) (t : ℝ) (z : Sphere)
    {m n : ℕ} (hm : readoutCoeff i (predictedClock D m t z) ≠ 0)
    (hn : readoutCoeff i (predictedClock D n t z) ≠ 0) : m = n := by
  apply clock_readout_unique (predictedClock_monotone D hgate0 t z)
    (readoutInterval_length i) ?_ ?_ hm hn
  · intro r hr
    exact readoutCoeff_mem_interval i hr
  · intro k hk
    have hr := readoutInterval_subset i (readoutCoeff_mem_interval i hk)
    exact predictedClock_unit_step D k t z (by linarith [hr.1]) (by linarith [hr.2])

theorem predictedClock_readout_single_hit (D : SphereData)
    (hgate0 : ∀ z, 0 ≤ D.gate z) (i : Fin 3) (t : ℝ) (z : Sphere)
    {j : ℕ} (hj : readoutCoeff i (predictedClock D j t z) ≠ 0) (n : ℕ) :
    readoutCoeff i (predictedClock D n t z) =
      if n = j then readoutCoeff i (predictedClock D j t z) else 0 := by
  split_ifs with hnj
  · subst n; rfl
  · by_contra hn
    exact hnj (predictedClock_readout_unique D hgate0 i t z hn hj)

theorem prediction_iterate_add_period (D : SphereData) (n : ℕ) (t : ℝ) (z : Sphere) :
    (prediction D)^[n] (t + 100, z) =
      (((prediction D)^[n] (t, z)).1 + 100, ((prediction D)^[n] (t, z)).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [prediction]
    have hp := Clock.increment_periodic (D.gate (((prediction D)^[n] (t, z)).2))
      (((prediction D)^[n] (t, z)).1)
    dsimp only at hp
    rw [hp]
    congr 1
    ring

theorem predictedClock_add_period (D : SphereData) (n : ℕ) (t : ℝ) (z : Sphere) :
    predictedClock D n (t + 100) z = predictedClock D n t z + 100 := by
  exact congrArg Prod.fst (prediction_iterate_add_period D n t z)

theorem increment_eq_one_on_readout_window {t : ℝ} (hlo : 70 ≤ t) (hhi : t ≤ 82)
    (e : ℝ) : Clock.increment t e = 1 := by
  apply Clock.increment_eq_one_of_barrier_eq_one
  apply Clock.barrier_plateau (by linarith) (by linarith)
  rw [abs_of_nonneg (by linarith : 0 ≤ t - 50)]
  linarith

theorem predictedClock_eq_actual_until_readout_end (D : SphereData)
    (x : ℕ → ℝ × Sphere) (t : ℝ) (z : Sphere) (N : ℕ)
    (hzero : x 0 = (t, z))
    (hclock : ∀ n, (x (n + 1)).1 = (x n).1 + Clock.increment (x n).1 (D.gate (x n).2))
    (hmain : ∀ n < N, (x n).1 < 70 → (x (n + 1)).2 = perturbedSquare 0 (x n).2)
    (hbound : ∀ n < N, (x n).1 ≤ 82) :
    ∀ n ≤ N, (x n).1 = predictedClock D n t z := by
  apply clock_prediction_agreement (x := x)
    (y := fun n => (prediction D)^[n] (t, z)) (clock := Prod.fst) (a := 70) (b := 82)
  · exact hzero
  · intro n hn heq hlo
    rw [Function.iterate_succ_apply']
    apply Prod.ext
    · change (x (n + 1)).1 =
        ((prediction D)^[n] (t, z)).1 +
          Clock.increment ((prediction D)^[n] (t, z)).1
            (D.gate ((prediction D)^[n] (t, z)).2)
      rw [hclock n, heq]
    · change (x (n + 1)).2 = perturbedSquare 0 ((prediction D)^[n] (t, z)).2
      rw [hmain n hn hlo, heq]
  · intro n _ hlo hhi
    rw [hclock n, increment_eq_one_on_readout_window hlo hhi]
  · intro n _ hlo hhi
    change predictedClock D (n + 1) t z = predictedClock D n t z + 1
    exact predictedClock_unit_step D n t z hlo hhi
  · exact hbound

theorem readoutCoeff_predictedClock_eq_actual (D : SphereData)
    (hgate0 : ∀ z, 0 ≤ D.gate z)
    (x : ℕ → ℝ × Sphere) (t : ℝ) (z : Sphere) (N : ℕ)
    (hzero : x 0 = (t, z))
    (hclock : ∀ n, (x (n + 1)).1 = (x n).1 + Clock.increment (x n).1 (D.gate (x n).2))
    (hmain : ∀ n < N, (x n).1 < 70 → (x (n + 1)).2 = perturbedSquare 0 (x n).2)
    (hbound : ∀ n < N, (x n).1 ≤ 82) (hN : 82 ≤ (x N).1)
    (i : Fin 3) : ∀ n, readoutCoeff i ((x n).1) = readoutCoeff i (predictedClock D n t z) := by
  have hxmono : Monotone (fun n => (x n).1) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hclock n]
    exact le_add_of_nonneg_right (Clock.increment_nonneg _ (hgate0 _))
  apply clock_readout_values_agree hxmono (predictedClock_monotone D hgate0 t z)
    (b := 82) ?_ N hN
    (predictedClock_eq_actual_until_readout_end D x t z N hzero hclock hmain hbound)
  intro r hr
  by_contra hβ
  have hs := readoutInterval_subset i (readoutCoeff_mem_interval i hβ)
  linarith [hs.2]

end Problem340.Construction

end

end OAI
