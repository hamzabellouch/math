import Mathlib

namespace OAI

open Filter Set
open scoped Topology

namespace Problem340.ClockDynamics

theorem bounded_clock_limit {t : ℕ → ℝ}
    (hmono : Monotone t) (hbounded : BddAbove (Set.range t)) :
    ∃ T : ℝ, Tendsto t atTop (𝓝 T) ∧
      Tendsto (fun n => t (n + 1) - t n) atTop (𝓝 0) := by
  have hlimit : Tendsto t atTop (𝓝 (⨆ n, t n)) :=
    tendsto_atTop_ciSup hmono hbounded
  refine ⟨⨆ n, t n, hlimit, ?_⟩
  have hnext : Tendsto (fun n => t (n + 1)) atTop (𝓝 (⨆ n, t n)) :=
    hlimit.comp (tendsto_add_atTop_nat 1)
  simpa using hnext.sub hlimit

theorem bounded_clock_limit_barrier {t : ℕ → ℝ} {b : ℝ → ℝ}
    (hmono : Monotone t) (hbounded : BddAbove (Set.range t))
    (hb : Continuous b) (hb_nonneg : ∀ x, 0 ≤ b x)
    (hstep : ∀ n, b (t n) ≤ t (n + 1) - t n) :
    ∃ T : ℝ, Tendsto t atTop (𝓝 T) ∧ b T = 0 := by
  obtain ⟨T, hlimit, hdiff⟩ := bounded_clock_limit hmono hbounded
  refine ⟨T, hlimit, ?_⟩
  have hzero : Tendsto (fun n => b (t n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => hb_nonneg (t n)) hstep hdiff
  exact tendsto_nhds_unique (hb.tendsto T |>.comp hlimit) hzero

theorem bounded_clock_limit_lattice {t : ℕ → ℝ} {b : ℝ → ℝ}
    (hmono : Monotone t) (hbounded : BddAbove (Set.range t))
    (hb : Continuous b) (hb_nonneg : ∀ x, 0 ≤ b x)
    (hstep : ∀ n, b (t n) ≤ t (n + 1) - t n)
    (hzeros : ∀ x, b x = 0 → ∃ k : ℤ, x = 50 + 100 * (k : ℝ)) :
    ∃ k : ℤ, Tendsto t atTop (𝓝 (50 + 100 * (k : ℝ))) := by
  obtain ⟨T, hlimit, hzero⟩ :=
    bounded_clock_limit_barrier hmono hbounded hb hb_nonneg hstep
  obtain ⟨k, rfl⟩ := hzeros T hzero
  exact ⟨k, hlimit⟩

theorem monotone_of_nonneg_increments {t : ℕ → ℝ}
    (hstep : ∀ n, 0 ≤ t (n + 1) - t n) : Monotone t := by
  apply monotone_nat_of_le_succ
  intro n
  linarith [hstep n]

theorem barrier_trapping {t r : ℕ → ℝ} {a T R : ℝ} {N : ℕ}
    (htN : a ≤ t N ∧ t N ≤ T) (hrN : r N ≤ R)
    (hstep : ∀ n, N ≤ n → a ≤ t n → t n ≤ T → r n ≤ R →
      (a ≤ t (n + 1) ∧ t (n + 1) ≤ T) ∧ r (n + 1) ≤ R) :
    ∀ n, N ≤ n → (a ≤ t n ∧ t n ≤ T) ∧ r n ≤ R := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact ⟨htN, hrN⟩
  | succ n hn ih => exact hstep n hn ih.1.1 ih.1.2 ih.2

theorem exists_first_crossing {t : ℕ → ℝ} {a : ℝ}
    (hstart : t 0 < a) (hstep : ∀ n, t (n + 1) - t n ≤ 1)
    (hevent : ∃ n, a ≤ t n) :
    ∃ n, a ≤ t n ∧ t n < a + 1 ∧ ∀ m, m < n → t m < a := by
  classical
  let n := Nat.find hevent
  have hn : a ≤ t n := Nat.find_spec hevent
  have hbefore : ∀ m, m < n → t m < a := by
    intro m hm
    exact lt_of_not_ge (Nat.find_min hevent hm)
  have hnpos : 0 < n := by
    by_contra h
    have hnzero : n = 0 := by omega
    rw [hnzero] at hn
    linarith
  refine ⟨n, hn, ?_, hbefore⟩
  have hp : t (n - 1) < a := hbefore (n - 1) (by omega)
  have hs := hstep (n - 1)
  have heq : n - 1 + 1 = n := by omega
  rw [heq] at hs
  linarith

theorem single_visit_short_interval {t : ℕ → ℝ} {a b : ℝ}
    (hmono : Monotone t) (hwidth : b - a ≤ 1)
    (hstep : ∀ n, a < t n → t n < b → t (n + 1) = t n + 1)
    {i j : ℕ} (hi : a < t i ∧ t i < b) (hj : a < t j ∧ t j < b) : i = j := by
  have hnotlt : ∀ i j, a < t i ∧ t i < b → a < t j ∧ t j < b → ¬ i < j := by
    intro i j hi hj hij
    have hle := hmono (Nat.succ_le_of_lt hij)
    rw [hstep i hi.1 hi.2] at hle
    linarith
  exact Nat.le_antisymm (Nat.le_of_not_gt (hnotlt j i hj hi))
    (Nat.le_of_not_gt (hnotlt i j hi hj))

theorem squaring_tendsto_zero {R : Type*} [SeminormedRing R] {z : ℕ → R}
    (hstep : ∀ n, z (n + 1) = z n ^ 2) (hsmall : ‖z 0‖ < 1) :
    Tendsto z atTop (𝓝 0) := by
  have hformula : ∀ n, z n = z 0 ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [hstep, ih, ← pow_mul, Nat.pow_succ]
  have hpower := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hsmall).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))
  exact hpower.congr (fun n => (hformula n).symm)

theorem eventually_squaring_tendsto_zero {R : Type*} [SeminormedRing R]
    {z : ℕ → R} (hstep : ∀ᶠ n in atTop, z (n + 1) = z n ^ 2)
    (hsmall : ∀ᶠ n in atTop, ‖z n‖ < 1) : Tendsto z atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hstep.and hsmall)
  apply (tendsto_add_atTop_iff_nat N).mp
  apply squaring_tendsto_zero
  · intro n
    have h := (hN (n + N) (by omega)).1
    convert h using 1
    congr 1
    omega
  · simpa using (hN N le_rfl).2

theorem eventually_small_of_bounded_clock {t r : ℕ → ℝ} {R c : ℝ}
    (hmono : Monotone t) (hbounded : BddAbove (Set.range t)) (hc : 0 < c)
    (hfast : ∀ n, R ≤ r n → c ≤ t (n + 1) - t n) :
    ∀ᶠ n in atTop, r n < R := by
  obtain ⟨T, hlimit, hdiff⟩ := bounded_clock_limit hmono hbounded
  have hsmall := hdiff.eventually (gt_mem_nhds hc)
  filter_upwards [hsmall] with n hn
  by_contra h
  exact (not_le_of_gt hn) (hfast n (le_of_not_gt h))

theorem bounded_clock_eventually_squaring_tendsto_zero
    {R : Type*} [SeminormedRing R] {t : ℕ → ℝ} {z : ℕ → R} {r c : ℝ}
    (hmono : Monotone t) (hbounded : BddAbove (Set.range t))
    (hc : 0 < c) (hr : r ≤ 1)
    (hfast : ∀ n, r ≤ ‖z n‖ → c ≤ t (n + 1) - t n)
    (hstep : ∀ᶠ n in atTop, z (n + 1) = z n ^ 2) :
    Tendsto z atTop (𝓝 0) := by
  apply eventually_squaring_tendsto_zero hstep
  filter_upwards [eventually_small_of_bounded_clock hmono hbounded hc hfast] with n hn
  exact hn.trans_le hr

theorem preparation_norm_gt_half {t : ℕ → ℝ} {z : ℕ → ℂ} {N : ℕ}
    (hmono : Monotone t) (hunbounded : ¬ BddAbove (Set.range t))
    (hstart : 8 ≤ t N ∧ t N ≤ 50)
    (htrap : ∀ n, N ≤ n → 8 ≤ t n → t n ≤ 50 → ‖z n‖ ≤ 1 / 2 →
      t (n + 1) ≤ 50 ∧ z (n + 1) = z n ^ 2) :
    1 / 2 < ‖z N‖ := by
  by_contra h
  have hsmall : ‖z N‖ ≤ 1 / 2 := le_of_not_gt h
  have hinvariant : ∀ n, N ≤ n → (8 ≤ t n ∧ t n ≤ 50) ∧ ‖z n‖ ≤ 1 / 2 := by
    apply barrier_trapping hstart hsmall
    intro n hn hlow hhigh hz
    obtain ⟨hclock, hsquare⟩ := htrap n hn hlow hhigh hz
    refine ⟨⟨hlow.trans (hmono (Nat.le_succ n)), hclock⟩, ?_⟩
    rw [hsquare, norm_pow]
    nlinarith [norm_nonneg (z n)]
  apply hunbounded
  refine ⟨50, ?_⟩
  rintro x ⟨n, rfl⟩
  by_cases hn : N ≤ n
  · exact (hinvariant n hn).1.2
  · exact (hmono (le_of_not_ge hn)).trans hstart.2

theorem exists_crossing_after {t : ℕ → ℝ} {N : ℕ} {a : ℝ}
    (hmono : Monotone t) (hunbounded : ¬ BddAbove (Set.range t))
    (hstart : t N < a) (hstep : ∀ n, t (n + 1) - t n ≤ 1) :
    ∃ n, N ≤ n ∧ a ≤ t n ∧ t n < a + 1 := by
  have hevent : ∃ n, a ≤ t (n + N) := by
    obtain ⟨x, ⟨m, rfl⟩, hm⟩ := not_bddAbove_iff.mp hunbounded a
    exact ⟨m, hm.le.trans (hmono (by omega))⟩
  have hstep' : ∀ n, t ((n + 1) + N) - t (n + N) ≤ 1 := by
    intro n
    simpa only [Nat.add_right_comm] using hstep (n + N)
  obtain ⟨n, hlow, hhigh, _⟩ :=
    exists_first_crossing (t := fun n => t (n + N)) (by simpa using hstart) hstep' hevent
  exact ⟨n + N, by omega, hlow, hhigh⟩

theorem exists_later_periodic_reset {t : ℕ → ℝ} (hmono : Monotone t)
    (hunbounded : ¬ BddAbove (Set.range t))
    (hstep : ∀ n, t (n + 1) - t n ≤ 1) (N : ℕ) :
    ∃ n ≥ N, ∃ k : ℤ, 2 + 100 * (k : ℝ) ≤ t n ∧ t n < 3 + 100 * (k : ℝ) := by
  obtain ⟨k, hk⟩ := exists_int_gt ((t N - 2) / 100)
  have hstart : t N < 2 + 100 * (k : ℝ) := by linarith
  obtain ⟨n, hn, hlow, hhigh⟩ := exists_crossing_after hmono hunbounded hstart hstep
  refine ⟨n, hn, k, hlow, ?_⟩
  linarith

theorem eventually_zero_after_periodic_reset {V : Type*} [Zero V]
    {t : ℕ → ℝ} {v : ℕ → V} (hmono : Monotone t)
    (hunbounded : ¬ BddAbove (Set.range t))
    (hstep : ∀ n, t (n + 1) - t n ≤ 1)
    (hstay : ∀ᶠ n in atTop, v n = 0 → v (n + 1) = 0)
    (hreset : ∀ n (k : ℤ), 2 + 100 * (k : ℝ) ≤ t n →
      t n ≤ 5 + 100 * (k : ℝ) → v (n + 1) = 0) :
    ∀ᶠ n in atTop, v n = 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hstay
  obtain ⟨n, hn, k, hlow, hhigh⟩ := exists_later_periodic_reset hmono hunbounded hstep N
  have hzero : v (n + 1) = 0 := hreset n k hlow (by linarith)
  apply eventually_atTop.mpr
  refine ⟨n + 1, ?_⟩
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hzero
  | succ m hm ih => exact hN m (by omega) ih

end Problem340.ClockDynamics

end OAI
