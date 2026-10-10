import OAI.Dynamics.EntropyCounterexample.PredictionClock

namespace OAI

noncomputable section

namespace Problem340.Construction.PredictionAgreement

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem periodicReadout_coe_on_strip (i : Fin 3) {t : ℝ}
    (h0 : 0 ≤ t) (h100 : t < 100) :
    periodicReadout i (t : AddCircle (100 : ℝ)) = readoutCoeff i t := by
  exact AddCircle.liftIco_zero_coe_apply ⟨h0, h100⟩

theorem readout_zero_before_window (D : SphereData) {t : ℝ}
    (h0 : 0 ≤ t) (h70 : t < 70) (v : Fin 3 → Sphere) :
    readout D (t : AddCircle (100 : ℝ)) v = 0 := by
  have hβ : ∀ i : Fin 3, readoutCoeff i t = 0 := by
    intro i
    by_contra hi
    have hs := readoutInterval_subset i (readoutCoeff_mem_interval i hi)
    linarith [hs.1]
  simp only [readout, periodicReadout_coe_on_strip _ h0 (by linarith), hβ,
    Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, mul_zero]

theorem rawMap_main_squares_before_window (D : SphereData) (x : RawManifold) {t : ℝ}
    (hclock : x.1 = (t : AddCircle (100 : ℝ))) (h0 : 0 ≤ t) (h70 : t < 70) :
    (rawMap D x).2.1 = perturbedSquare 0 x.2.1 := by
  change perturbedSquare (readout D x.1 x.2.2) x.2.1 = perturbedSquare 0 x.2.1
  rw [hclock, readout_zero_before_window D h0 h70]

theorem readout_agreement_of_raw_orbit (D : SphereData)
    (hgate0 : ∀ z, 0 ≤ D.gate z)
    (x : ℕ → RawManifold) (t : ℕ → ℝ)
    (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (hprojection : ∀ n, (x n).1 = (t n : AddCircle (100 : ℝ)))
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (x n).2.1))
    (hstart : 0 ≤ t 0) (N : ℕ)
    (hbefore : ∀ n < N, t n ≤ 82) (hexit : 82 ≤ t N)
    (i : Fin 3) :
    ∀ n, readoutCoeff i (t n) = readoutCoeff i (predictedClock D n (t 0) (x 0).2.1) := by
  have htmono : Monotone t := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hclock n]
    exact le_add_of_nonneg_right (Clock.increment_nonneg _ (hgate0 _))
  apply readoutCoeff_predictedClock_eq_actual D hgate0
    (fun n => (t n, (x n).2.1)) (t 0) (x 0).2.1 N rfl
  · exact hclock
  · intro n _ hn
    change (x (n + 1)).2.1 = perturbedSquare 0 (x n).2.1
    rw [horbit n]
    exact rawMap_main_squares_before_window D (x n) (hprojection n)
      (hstart.trans (htmono (Nat.zero_le n))) hn
  · exact hbefore
  · exact hexit

theorem single_hit_of_raw_orbit (D : SphereData)
    (hgate0 : ∀ z, 0 ≤ D.gate z)
    (x : ℕ → RawManifold) (t : ℕ → ℝ)
    (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (hprojection : ∀ n, (x n).1 = (t n : AddCircle (100 : ℝ)))
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (x n).2.1))
    (hstart : 0 ≤ t 0) (N : ℕ)
    (hbefore : ∀ n < N, t n ≤ 82) (hexit : 82 ≤ t N)
    (i : Fin 3) {j : ℕ} (hj : readoutCoeff i (t j) ≠ 0) (n : ℕ) :
    readoutCoeff i (predictedClock D n (t 0) (x 0).2.1) =
      if n = j then readoutCoeff i (t j) else 0 := by
  have hagree := readout_agreement_of_raw_orbit D hgate0 x t horbit hprojection
    hclock hstart N hbefore hexit i
  have hpj : readoutCoeff i (predictedClock D j (t 0) (x 0).2.1) ≠ 0 := by
    rw [← hagree j]
    exact hj
  rw [predictedClock_readout_single_hit D hgate0 i (t 0) (x 0).2.1 hpj n, ← hagree j]

theorem readout_agreement_of_unbounded_raw_orbit (D : SphereData)
    (hgate0 : ∀ z, 0 ≤ D.gate z)
    (x : ℕ → RawManifold) (t : ℕ → ℝ)
    (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (hprojection : ∀ n, (x n).1 = (t n : AddCircle (100 : ℝ)))
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (x n).2.1))
    (hstart : 0 ≤ t 0) (hunbounded : ¬ BddAbove (Set.range t))
    (i : Fin 3) :
    ∀ n, readoutCoeff i (t n) = readoutCoeff i (predictedClock D n (t 0) (x 0).2.1) := by
  classical
  have hexit : ∃ n, 82 ≤ t n := by
    obtain ⟨r, ⟨n, rfl⟩, hn⟩ := not_bddAbove_iff.mp hunbounded 82
    exact ⟨n, hn.le⟩
  let N := Nat.find hexit
  have hN : 82 ≤ t N := Nat.find_spec hexit
  have hbefore : ∀ n < N, t n ≤ 82 := by
    intro n hn
    exact (lt_of_not_ge (Nat.find_min hexit hn)).le
  exact readout_agreement_of_raw_orbit D hgate0 x t horbit hprojection
    hclock hstart N hbefore hN i

theorem single_hit_of_unbounded_raw_orbit (D : SphereData)
    (hgate0 : ∀ z, 0 ≤ D.gate z)
    (x : ℕ → RawManifold) (t : ℕ → ℝ)
    (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (hprojection : ∀ n, (x n).1 = (t n : AddCircle (100 : ℝ)))
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (x n).2.1))
    (hstart : 0 ≤ t 0) (hunbounded : ¬ BddAbove (Set.range t))
    (i : Fin 3) {j : ℕ} (hj : readoutCoeff i (t j) ≠ 0) (n : ℕ) :
    readoutCoeff i (predictedClock D n (t 0) (x 0).2.1) =
      if n = j then readoutCoeff i (t j) else 0 := by
  have hagree := readout_agreement_of_unbounded_raw_orbit D hgate0 x t horbit
    hprojection hclock hstart hunbounded i
  have hpj : readoutCoeff i (predictedClock D j (t 0) (x 0).2.1) ≠ 0 := by
    rw [← hagree j]
    exact hj
  rw [predictedClock_readout_single_hit D hgate0 i (t 0) (x 0).2.1 hpj n, ← hagree j]

theorem predictedClock_eq_actual_of_le82 (D : SphereData)
    (hgate0 : ∀ z, 0 ≤ D.gate z)
    (x : ℕ → RawManifold) (t : ℕ → ℝ)
    (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (hprojection : ∀ n, (x n).1 = (t n : AddCircle (100 : ℝ)))
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (x n).2.1))
    (hstart : 0 ≤ t 0) {N : ℕ} (hN : t N ≤ 82) :
    predictedClock D N (t 0) (x 0).2.1 = t N := by
  have htmono : Monotone t := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hclock n]
    exact le_add_of_nonneg_right (Clock.increment_nonneg _ (hgate0 _))
  have hagree := predictedClock_eq_actual_until_readout_end D
    (fun n => (t n, (x n).2.1)) (t 0) (x 0).2.1 N rfl hclock
    (fun n _ hn => by
      change (x (n + 1)).2.1 = perturbedSquare 0 (x n).2.1
      rw [horbit n]
      exact rawMap_main_squares_before_window D (x n) (hprojection n)
        (hstart.trans (htmono (Nat.zero_le n))) hn)
    (fun n hn => (htmono hn.le).trans hN)
  exact (hagree N le_rfl).symm

theorem predictedClock_eq_actual_between (D : SphereData)
    (hgate0 : ∀ z, 0 ≤ D.gate z)
    (x : ℕ → RawManifold) (t : ℕ → ℝ)
    (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (hprojection : ∀ n, (x n).1 = (t n : AddCircle (100 : ℝ)))
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (x n).2.1))
    {i j : ℕ} (hij : i ≤ j) (hi : 0 ≤ t i) (hj : t j ≤ 82) :
    predictedClock D (j - i) (t i) (x i).2.1 = t j := by
  have hshiftOrbit : ∀ n, x (i + (n + 1)) = rawMap D (x (i + n)) := by
    intro n
    simpa only [Nat.add_assoc] using horbit (i + n)
  have hshiftClock : ∀ n, t (i + (n + 1)) = t (i + n) +
      Clock.increment (t (i + n)) (D.gate (x (i + n)).2.1) := by
    intro n
    simpa only [Nat.add_assoc] using hclock (i + n)
  have heq := predictedClock_eq_actual_of_le82 D hgate0
    (fun n => x (i + n)) (fun n => t (i + n)) hshiftOrbit
    (fun n => hprojection (i + n)) hshiftClock
    (by simpa using hi) (N := j - i) (by simpa [Nat.add_sub_of_le hij] using hj)
  simpa [Nat.add_sub_of_le hij] using heq

end Problem340.Construction.PredictionAgreement

end

end OAI
