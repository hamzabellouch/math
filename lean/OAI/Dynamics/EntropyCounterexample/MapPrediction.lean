import OAI.Dynamics.EntropyCounterexample.MapSignal

namespace OAI

noncomputable section

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem readout_eq_zero_before_region
    (D : SphereData) {t : ℝ} (ht0 : 0 ≤ t) (ht74 : t < 74)
    (v : Fin 3 → Sphere) :
    readout D (t : AddCircle (100 : ℝ)) v = 0 := by
  have hstrip : t ∈ Set.Ico 0 100 := ⟨ht0, by linarith⟩
  have hβ : ∀ ℓ : Fin 3, readoutCoeff ℓ t = 0 := by
    intro ℓ
    by_contra h
    have hmem : t ∈ readoutInterval ℓ := by
      rwa [← readoutCoeff_support, Function.mem_support]
    have hbounds := readoutInterval_subset ℓ hmem
    linarith [hbounds.1]
  simp only [readout, periodicReadout, AddCircle.liftIco_zero_coe_apply hstrip,
    hβ, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, mul_zero]

theorem increment_eq_one_on_readout_band {t e : ℝ}
    (ht : t ∈ Set.Icc 70 82) : Clock.increment t e = 1 := by
  apply Clock.increment_eq_one_of_barrier_eq_one
  apply Clock.barrier_plateau (by linarith [ht.1]) (by linarith [ht.2])
  rw [abs_of_nonneg (by linarith [ht.1])]
  linarith [ht.1]

theorem rawMap_predictedClock_at_readout
    (D : SphereData)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (t : ℕ → ℝ) (ht : Monotone t)
    (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (x n).2.1))
    (ℓ : Fin 3) (i j : ℕ) (hij : i ≤ j) (hti : 0 ≤ t i)
    (hread : readoutCoeff ℓ (t j) ≠ 0) :
    predictedClock D (j - i) (t i) (x i).2.1 = t j := by
  have hmem : t j ∈ readoutInterval ℓ := by
    rwa [← readoutCoeff_support, Function.mem_support]
  have hjbounds := readoutInterval_subset ℓ hmem
  let A : ℕ → ℝ × Sphere := fun n => (t (i + n), (x (i + n)).2.1)
  let P : ℕ → ℝ × Sphere := fun n => (prediction D)^[n] (t i, (x i).2.1)
  have hAstep : ∀ n, (A n).1 < 70 → A (n + 1) = prediction D (A n) := by
    intro n hn
    have htn0 : 0 ≤ t (i + n) := hti.trans (ht (by omega))
    have hzero : readout D (x (i + n)).1 (x (i + n)).2.2 = 0 := by
      rw [← hlift (i + n)]
      exact readout_eq_zero_before_region D htn0 (by change t (i + n) < 70 at hn; linarith) _
    apply Prod.ext
    · change t (i + (n + 1)) = t (i + n) +
        Clock.increment (t (i + n)) (D.gate (x (i + n)).2.1)
      simpa only [Nat.add_assoc] using hclock (i + n)
    · change (x (i + (n + 1))).2.1 = perturbedSquare 0 (x (i + n)).2.1
      rw [← Nat.add_assoc, horbit (i + n)]
      change perturbedSquare (readout D (x (i + n)).1 (x (i + n)).2.2)
        (x (i + n)).2.1 = _
      rw [hzero]
  have hPstep : ∀ n, P (n + 1) = prediction D (P n) := by
    intro n
    exact Function.iterate_succ_apply' (prediction D) n _
  have hagree : ∀ n ≤ j - i, (A n).1 = (P n).1 := by
    apply clock_prediction_agreement (clock := Prod.fst) (a := 70) (b := 82)
    · simp [A, P]
    · intro n _ heq hn
      rw [hAstep n hn, hPstep n, heq]
    · intro n _ hn0 hn1
      change t (i + (n + 1)) = t (i + n) + 1
      rw [← Nat.add_assoc, hclock (i + n),
        increment_eq_one_on_readout_band ⟨hn0, hn1⟩]
    · intro n _ hn0 hn1
      rw [hPstep n]
      change (P n).1 + Clock.increment (P n).1 (D.gate (P n).2) = (P n).1 + 1
      rw [increment_eq_one_on_readout_band ⟨hn0, hn1⟩]
    · intro n hn
      have hnt : t (i + n) ≤ t j := ht (by omega)
      change t (i + n) ≤ 82
      linarith [hjbounds.2]
  have hfinal := (hagree (j - i) le_rfl).symm
  simpa only [A, P, predictedClock, Nat.add_sub_of_le hij] using hfinal

end Problem340.Construction

end

end OAI
