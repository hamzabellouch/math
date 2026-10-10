import Mathlib

namespace OAI

noncomputable section

open Filter

namespace Problem340.RegisterErasure

theorem recurring_periodic_window
    (t : ℕ → ℝ) (ht : Monotone t) (hunbounded : Tendsto t atTop atTop)
    {P d : ℝ} (hP : 0 < P)
    (hstep : ∀ n, t (n + 1) ≤ t n + d) (a : ℝ) (N : ℕ) :
    ∃ n ≥ N, ∃ k : ℤ, t n ∈ Set.Icc (a + P * (k : ℝ)) (a + P * (k : ℝ) + d) := by
  obtain ⟨k, hk⟩ := exists_int_gt ((t N - a) / P)
  have hthreshold : t N < a + P * (k : ℝ) := by
    have := (div_lt_iff₀ hP).mp hk
    nlinarith
  have hex : ∃ n, a + P * (k : ℝ) ≤ t n :=
    (hunbounded.eventually_ge_atTop (a + P * (k : ℝ))).exists
  let n := Nat.find hex
  have hn : a + P * (k : ℝ) ≤ t n := Nat.find_spec hex
  have hN : N < n := by
    by_contra h
    have hle : n ≤ N := by omega
    exact (not_le_of_gt hthreshold) (hn.trans (ht hle))
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hprev : t m < a + P * (k : ℝ) := by
    apply lt_of_not_ge
    exact Nat.find_min hex (by dsimp [n] at hm; omega)
  refine ⟨n, hN.le, k, hn, ?_⟩
  rw [hm]
  linarith [hstep m]

theorem recurring_zero_gain
    (t a : ℕ → ℝ) (ht : Monotone t) (hunbounded : Tendsto t atTop atTop)
    (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    (hreset : ∀ n (k : ℤ), t n ∈ Set.Icc (2 + 100 * (k : ℝ)) (5 + 100 * (k : ℝ)) → a n = 0) :
    ∀ N, ∃ n ≥ N, a n = 0 := by
  intro N
  obtain ⟨n, hn, k, hlo, hhi⟩ := recurring_periodic_window t ht hunbounded
    (show (0 : ℝ) < 100 by norm_num) hstep 2 N
  exact ⟨n, hn, hreset n k ⟨hlo, by linarith⟩⟩

theorem gain_zero_on_lifted_reset_window
    (A : ℝ → ℝ) (hper : Function.Periodic A 100)
    (hzero : ∀ s ∈ Set.Icc (2 : ℝ) 5, A s = 0)
    (t : ℝ) (k : ℤ)
    (ht : t ∈ Set.Icc (2 + 100 * (k : ℝ)) (5 + 100 * (k : ℝ))) :
    A t = 0 := by
  rw [← hper.sub_int_mul_eq k]
  apply hzero
  constructor <;> nlinarith [ht.1, ht.2]

theorem recurring_zero_periodic_gain
    (t : ℕ → ℝ) (A : ℝ → ℝ) (hper : Function.Periodic A 100)
    (hzero : ∀ s ∈ Set.Icc (2 : ℝ) 5, A s = 0)
    (ht : Monotone t) (htop : Tendsto t atTop atTop)
    (hstep : ∀ n, t (n + 1) ≤ t n + 1) :
    ∀ N, ∃ n ≥ N, A (t n) = 0 := by
  apply recurring_zero_gain t (fun n => A (t n)) ht htop hstep
  intro n k hn
  exact gain_zero_on_lifted_reset_window A hper hzero (t n) k hn

theorem eventually_zero_of_recurring_reset
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (S : E → E) (hS : S 0 = 0) (a : ℕ → ℝ) (u v : ℕ → E)
    (hrec : ∀ n, v (n + 1) = a n • S (v n) + u n)
    (hu : ∀ᶠ n in atTop, u n = 0)
    (hreset : ∀ N, ∃ n ≥ N, a n = 0) :
    ∀ᶠ n in atTop, v n = 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  obtain ⟨r, hr, ha⟩ := hreset N
  have hzero : v (r + 1) = 0 := by rw [hrec, ha, zero_smul, hN r hr, add_zero]
  apply eventually_atTop.mpr
  refine ⟨r + 1, ?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hzero
  | succ n hn ih =>
      rw [hrec, ih, hS, smul_zero, hN n (by omega), add_zero]

theorem eventually_cutoff_zero_of_norm_escape
    {E F : Type*} [SeminormedAddGroup E] [Zero F]
    (χ : E → F) (hχ : HasCompactSupport χ) (z : ℕ → E)
    (hz : Tendsto (fun n => ‖z n‖) atTop atTop) :
    ∀ᶠ n in atTop, χ (z n) = 0 := by
  obtain ⟨R, hR⟩ := hχ.isCompact.isBounded.exists_norm_le
  filter_upwards [hz.eventually_gt_atTop R] with n hn
  by_contra hne
  exact (not_le_of_gt hn) (hR (z n) (subset_tsupport χ hne))

theorem eventually_base_of_recurring_reset
    {E X : Type*} [AddCommGroup E] [Module ℝ E]
    (base : X) (embed : E → X) (hembed : embed 0 = base)
    (S : X → E) (hS : S base = 0) (a : ℕ → ℝ) (u : ℕ → E) (v : ℕ → X)
    (hrec : ∀ n, v (n + 1) = embed (a n • S (v n) + u n))
    (hu : ∀ᶠ n in atTop, u n = 0)
    (hreset : ∀ N, ∃ n ≥ N, a n = 0) :
    ∀ᶠ n in atTop, v n = base := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  obtain ⟨r, hr, ha⟩ := hreset N
  have hzero : v (r + 1) = base := by
    rw [hrec, ha, zero_smul, hN r hr, add_zero, hembed]
  apply eventually_atTop.mpr
  refine ⟨r + 1, ?_⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hzero
  | succ n hn ih =>
      rw [hrec, ih, hS, smul_zero, hN n (by omega), add_zero, hembed]

theorem eventually_all_base_of_recurring_reset
    {ι E X : Type*} [AddCommGroup E] [Module ℝ E]
    (base : X) (embed : E → X) (hembed : embed 0 = base)
    (S : X → E) (hS : S base = 0) (a : ℕ → ℝ)
    (u : ℕ → ι → E) (v : ℕ → ι → X)
    (hrec : ∀ n i, v (n + 1) i = embed (a n • S (v n i) + u n i))
    (hu : ∀ᶠ n in atTop, ∀ i, u n i = 0)
    (hreset : ∀ N, ∃ n ≥ N, a n = 0) :
    ∀ᶠ n in atTop, ∀ i, v n i = base := by
  have hp := eventually_base_of_recurring_reset
    (fun _ : ι => base) (fun w : ι → E => fun i => embed (w i))
    (by ext i; exact hembed)
    (fun w : ι → X => fun i => S (w i)) (by ext i; exact hS)
    a u v (fun n => funext (hrec n))
    (hu.mono (fun n hn => funext hn)) hreset
  exact hp.mono (fun n hn i => congrFun hn i)

theorem eventually_registers_erased_of_escape
    {ι E X Y F : Type*} [AddCommGroup E] [Module ℝ E]
    [SeminormedAddGroup Y] [Zero F]
    (base : X) (embed : E → X) (hembed : embed 0 = base)
    (S : X → E) (hS : S base = 0)
    (t a : ℕ → ℝ) (z : ℕ → Y) (χ : Y → F) (hχ : HasCompactSupport χ)
    (u : ℕ → ι → E) (v : ℕ → ι → X)
    (ht : Monotone t) (htop : Tendsto t atTop atTop)
    (hstep : ∀ n, t (n + 1) ≤ t n + 1)
    (hreset : ∀ n (k : ℤ), t n ∈ Set.Icc (2 + 100 * (k : ℝ)) (5 + 100 * (k : ℝ)) → a n = 0)
    (hz : Tendsto (fun n => ‖z n‖) atTop atTop)
    (hinput : ∀ n, χ (z n) = 0 → ∀ i, u n i = 0)
    (hrec : ∀ n i, v (n + 1) i = embed (a n • S (v n i) + u n i)) :
    ∀ᶠ n in atTop, ∀ i, v n i = base := by
  apply eventually_all_base_of_recurring_reset base embed hembed S hS a u v hrec
  · exact (eventually_cutoff_zero_of_norm_escape χ hχ z hz).mono hinput
  · exact recurring_zero_gain t a ht htop hstep hreset

end Problem340.RegisterErasure

end

end OAI
