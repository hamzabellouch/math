import OAI.Dynamics.EntropyCounterexample.ClockDynamics
import OAI.Dynamics.EntropyCounterexample.ClockPrediction

namespace OAI

namespace Problem340

theorem exists_complete_clock_passage {t : ℕ → ℝ} {a : ℝ}
    (hmono : Monotone t) (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    (hstart : t 0 < a) (hunbounded : ∀ A : ℝ, ∃ n, A ≤ t n) :
    ∃ lo hi : ℕ, lo < hi ∧
      a ≤ t lo ∧ t lo < a + 1 ∧
      a + 100 ≤ t hi ∧ t hi < a + 101 ∧
      ∀ n, lo ≤ n → n < hi → a ≤ t n ∧ t n < a + 100 := by
  have hstep' : ∀ n, t (n + 1) - t n ≤ 1 := by
    intro n
    linarith [hstep n]
  obtain ⟨lo, hlo, hloupper, _⟩ :=
    ClockDynamics.exists_first_crossing hstart hstep' (hunbounded a)
  obtain ⟨hi, hhi, hhiupper, hminimal⟩ := ClockDynamics.exists_first_crossing
    (show t 0 < a + 100 by linarith) hstep' (hunbounded (a + 100))
  have hlohi : lo < hi := by
    by_contra h
    have := hmono (show hi ≤ lo by omega)
    linarith
  refine ⟨lo, hi, hlohi, hlo, hloupper, hhi, by linarith, ?_⟩
  intro n hln hnh
  exact ⟨hlo.trans (hmono hln), hminimal n hnh⟩

theorem exists_clock_crossing_between {t : ℕ → ℝ} {a : ℝ}
    (hmono : Monotone t) (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hstart : t lo < a)
    (hend : a + 1 ≤ t hi) :
    ∃ n, lo ≤ n ∧ n < hi ∧ a ≤ t n ∧ t n < a + 1 := by
  obtain ⟨k, hklo, hkhi, _⟩ := ClockDynamics.exists_first_crossing
    (t := fun k => t (lo + k)) (a := a) (by simpa using hstart)
    (fun k => by
      have h := hstep (lo + k)
      simp only [Nat.add_assoc] at *
      linarith)
    ⟨hi - lo, by simpa [Nat.add_sub_of_le hlohi] using (by linarith : a ≤ t hi)⟩
  refine ⟨lo + k, by omega, ?_, hklo, hkhi⟩
  by_contra h
  have := hmono (show hi ≤ lo + k by omega)
  linarith

theorem exists_preparation_plateau {t : ℕ → ℝ} {α : ℝ → ℝ}
    (hmono : Monotone t) (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hstart : t lo < 1) (hend : 100 ≤ t hi)
    (hplateau : ∀ x, 9 ≤ x → x ≤ 11 → α x = 1) :
    ∃ i ∈ Finset.Ico lo hi, α (t i) = 1 := by
  obtain ⟨i, hlo, hhi, h9, h10⟩ := exists_clock_crossing_between hmono hstep
    hlohi (show t lo < 9 by linarith) (show (9 : ℝ) + 1 ≤ t hi by linarith)
  exact ⟨i, Finset.mem_Ico.mpr ⟨hlo, hhi⟩, hplateau _ h9 (by linarith)⟩

theorem preparation_indices_properties {t : ℕ → ℝ} {α : ℝ → ℝ}
    (hmono : Monotone t) (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hstart : t lo < 1) (hend : 100 ≤ t hi)
    (hsupport : ∀ x, 0 < α x → 8 < x ∧ x < 12)
    (hplateau : ∀ x, 9 ≤ x → x ≤ 11 → α x = 1)
    (hunit : ∀ n, 8 ≤ t n → t n ≤ 12 → t (n + 1) = t n + 1) :
    let I := (Finset.Ico lo hi).filter (fun i => 0 < α (t i))
    I.Nonempty ∧ I.card ≤ 5 ∧ ∃ i ∈ I, α (t i) = 1 := by
  classical
  let I := (Finset.Ico lo hi).filter (fun i => 0 < α (t i))
  obtain ⟨i, hiI, hiα⟩ := exists_preparation_plateau hmono hstep hlohi hstart hend hplateau
  have himem : i ∈ I := Finset.mem_filter.mpr ⟨hiI, by rw [hiα]; norm_num⟩
  have hcard : I.card ≤ 5 := by
    apply clock_preparation_card_le_five hmono hunit I
    intro n hn
    exact hsupport (t n) (Finset.mem_filter.mp hn).2
  change I.Nonempty ∧ I.card ≤ 5 ∧ ∃ i ∈ I, α (t i) = 1
  exact ⟨⟨i, himem⟩, by omega, i, himem, hiα⟩

theorem exists_reset_before_preparation {t : ℕ → ℝ}
    (hmono : Monotone t) (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hstart : t lo < 1) (hend : 100 ≤ t hi) :
    ∃ r ∈ Finset.Ico lo hi, 2 ≤ t r ∧ t r < 3 ∧
      ∀ i, 8 < t i → r + 1 ≤ i := by
  obtain ⟨r, hlo, hhi, h2, h3⟩ := exists_clock_crossing_between hmono hstep
    hlohi (show t lo < 2 by linarith) (show (2 : ℝ) + 1 ≤ t hi by linarith)
  refine ⟨r, Finset.mem_Ico.mpr ⟨hlo, hhi⟩, h2, by linarith, ?_⟩
  intro i hi
  by_contra h
  have := hmono (show i ≤ r by omega)
  linarith

theorem exists_readout_plateau {t : ℕ → ℝ} {ι : Type*} {β : ι → ℝ → ℝ}
    (hmono : Monotone t) (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hstart : t lo < 1) (hend : 100 ≤ t hi)
    (hcover : ∀ x, 76 ≤ x → x ≤ 77 → ∃ l, β l x = 1) :
    ∃ j ∈ Finset.Ico lo hi, 76 ≤ t j ∧ t j < 77 ∧ ∃ l, β l (t j) = 1 := by
  obtain ⟨j, hlo, hhi, h76, h77⟩ := exists_clock_crossing_between hmono hstep
    hlohi (show t lo < 76 by linarith) (show (76 : ℝ) + 1 ≤ t hi by linarith)
  refine ⟨j, Finset.mem_Ico.mpr ⟨hlo, hhi⟩, h76, by linarith, ?_⟩
  exact hcover _ h76 (by linarith)

theorem cofinal_clock_reset {E : Type*} [Zero E]
    {t : ℕ → ℝ} {gain : ℝ → E}
    (hmono : Monotone t) (hunbounded : ¬ BddAbove (Set.range t))
    (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    (hperiod : Function.Periodic gain 100)
    (hreset : ∀ x, 2 ≤ x → x ≤ 5 → gain x = 0) :
    ∀ N, ∃ n ≥ N, gain (t n) = 0 := by
  intro N
  obtain ⟨n, hn, k, hlow, hhigh⟩ := ClockDynamics.exists_later_periodic_reset
    hmono hunbounded (fun n => by linarith [hstep n]) N
  refine ⟨n, hn, ?_⟩
  rw [← hperiod.sub_int_mul_eq k]
  apply hreset <;> linarith

end Problem340

end OAI
