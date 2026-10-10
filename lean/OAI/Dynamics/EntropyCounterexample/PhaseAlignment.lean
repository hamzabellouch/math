import Mathlib

namespace OAI

noncomputable section

namespace Problem340

theorem aligned_square_norm
    (z θ : ℂ) (r c : ℝ) (hθ : ‖θ‖ = 1) (hz : z = (r : ℂ) * θ)
    (_hr : 0 ≤ r) (hc : 0 ≤ c) :
    ‖z ^ 2 + (c : ℂ) * θ ^ 2‖ = r ^ 2 + c := by
  rw [hz]
  have halign : ((r : ℂ) * θ) ^ 2 + (c : ℂ) * θ ^ 2 =
      ((r ^ 2 + c : ℝ) : ℂ) * θ ^ 2 := by push_cast; ring
  rw [halign, norm_mul, norm_pow, hθ, one_pow, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact add_nonneg (sq_nonneg r) hc

theorem aligned_square_ne_zero
    (z θ : ℂ) (r c : ℝ) (hθ : ‖θ‖ = 1) (hz : z = (r : ℂ) * θ)
    (hr : 0 < r) (hc : 0 ≤ c) :
    z ^ 2 + (c : ℂ) * θ ^ 2 ≠ 0 := by
  apply norm_pos_iff.mp
  rw [aligned_square_norm z θ r c hθ hz hr.le hc]
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) hc

theorem aligned_square_phase
    (z θ : ℂ) (r c : ℝ) (hθ : ‖θ‖ = 1) (hz : z = (r : ℂ) * θ)
    (hr : 0 < r) (hc : 0 ≤ c) :
    (z ^ 2 + (c : ℂ) * θ ^ 2) / ‖z ^ 2 + (c : ℂ) * θ ^ 2‖ = θ ^ 2 := by
  rw [aligned_square_norm z θ r c hθ hz hr.le hc, hz]
  have hp : r ^ 2 + c ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) hc)
  have hpC : ((r ^ 2 + c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp
  apply (div_eq_iff hpC).2
  push_cast
  ring

theorem pow_two_pow_le_of_square_le
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hstep : ∀ n, (r n) ^ 2 ≤ r (n + 1)) (n : ℕ) :
    (r 0) ^ (2 ^ n) ≤ r n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (r 0) ^ (2 ^ (n + 1)) = ((r 0) ^ (2 ^ n)) ^ 2 := by
          rw [pow_succ, pow_mul]
        _ ≤ (r n) ^ 2 := pow_le_pow_left₀ (pow_nonneg (hr 0) _) ih 2
        _ ≤ r (n + 1) := hstep n

theorem prediction_phase_power (θ : ℂ) (i j : ℕ) (hij : i ≤ j) :
    (θ ^ (2 ^ i)) ^ (2 ^ (j - i + 1)) = θ ^ (2 ^ (j + 1)) := by
  rw [← pow_mul, ← pow_add]
  congr 2
  omega

theorem tendsto_atTop_of_square_le
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hstep : ∀ n, (r n) ^ 2 ≤ r (n + 1)) (hinit : 1 < r 0) :
    Filter.Tendsto r Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono (pow_two_pow_le_of_square_le r hr hstep)
  exact (tendsto_pow_atTop_atTop_of_one_lt hinit).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))

theorem aligned_orbit_phase_until
    (z : ℕ → ℂ) (c : ℕ → ℝ) (θ : ℂ) (N : ℕ)
    (hθ : ‖θ‖ = 1) (hc : ∀ n, 0 ≤ c n)
    (hinit : z 0 = (‖z 0‖ : ℂ) * θ) (hz0 : z 0 ≠ 0)
    (hstep : ∀ n, n < N → z (n + 1) = z n ^ 2 + (c n : ℂ) * θ ^ (2 ^ (n + 1))) :
    ∀ n, n ≤ N → z n ≠ 0 ∧ z n = (‖z n‖ : ℂ) * θ ^ (2 ^ n) := by
  intro n
  induction n with
  | zero =>
      intro _
      simpa using And.intro hz0 hinit
  | succ n ih =>
      intro hnN
      have ih := ih (by omega)
      have hstepn := hstep n (by omega)
      have hu : ‖θ ^ (2 ^ n)‖ = 1 := by rw [norm_pow, hθ, one_pow]
      have hpow : θ ^ (2 ^ (n + 1)) = (θ ^ (2 ^ n)) ^ 2 := by
        rw [pow_succ, pow_mul]
      have hn : 0 < ‖z n‖ := norm_pos_iff.mpr ih.1
      have hnorm : ‖z (n + 1)‖ = ‖z n‖ ^ 2 + c n := by
        rw [hstepn, hpow]
        exact aligned_square_norm _ _ _ _ hu ih.2 hn.le (hc n)
      constructor
      · rw [hstepn, hpow]
        exact aligned_square_ne_zero _ _ _ _ hu ih.2 hn (hc n)
      · rw [hnorm]
        conv_lhs => rw [hstepn, ih.2]
        rw [hpow]
        push_cast
        ring

theorem aligned_orbit_phase
    (z : ℕ → ℂ) (c : ℕ → ℝ) (θ : ℂ)
    (hθ : ‖θ‖ = 1) (hc : ∀ n, 0 ≤ c n)
    (hinit : z 0 = (‖z 0‖ : ℂ) * θ) (hz0 : z 0 ≠ 0)
    (hstep : ∀ n, z (n + 1) = z n ^ 2 + (c n : ℂ) * θ ^ (2 ^ (n + 1))) :
    ∀ n, z n ≠ 0 ∧ z n = (‖z n‖ : ℂ) * θ ^ (2 ^ n) := by
  intro n
  exact aligned_orbit_phase_until z c θ n hθ hc hinit hz0
    (fun k _ => hstep k) n le_rfl

theorem aligned_orbit_norm
    (z : ℕ → ℂ) (c : ℕ → ℝ) (θ : ℂ)
    (hθ : ‖θ‖ = 1) (hc : ∀ n, 0 ≤ c n)
    (hinit : z 0 = (‖z 0‖ : ℂ) * θ) (hz0 : z 0 ≠ 0)
    (hstep : ∀ n, z (n + 1) = z n ^ 2 + (c n : ℂ) * θ ^ (2 ^ (n + 1)))
    (n : ℕ) :
    ‖z (n + 1)‖ = ‖z n‖ ^ 2 + c n := by
  have hi := aligned_orbit_phase z c θ hθ hc hinit hz0 hstep n
  have hu : ‖θ ^ (2 ^ n)‖ = 1 := by rw [norm_pow, hθ, one_pow]
  have hpow : θ ^ (2 ^ (n + 1)) = (θ ^ (2 ^ n)) ^ 2 := by
    rw [pow_succ, pow_mul]
  rw [hstep, hpow]
  exact aligned_square_norm _ _ _ _ hu hi.2 (norm_nonneg _) (hc n)

theorem aligned_readout_sum
    {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (a : ι → ℝ) (β : κ → ℝ) (v : κ → ℂ) (θ : ℂ)
    (hv : ∀ l ∈ J, v l = ((β l / 10 : ℝ) : ℂ) *
      ∑ i ∈ I, (a i : ℂ) * θ) :
    (20 : ℂ) * (∑ l ∈ J, (β l : ℂ) * v l) =
      ((2 * (∑ l ∈ J, β l ^ 2) * (∑ i ∈ I, a i) : ℝ) : ℂ) * θ := by
  have hs : (∑ l ∈ J, (β l : ℂ) * v l) =
      ((∑ l ∈ J, (β l : ℂ) ^ 2) / 10) *
        (∑ i ∈ I, (a i : ℂ)) * θ := by
    calc
      (∑ l ∈ J, (β l : ℂ) * v l) =
          ∑ l ∈ J, ((β l : ℂ) ^ 2 / 10) *
            (∑ i ∈ I, (a i : ℂ)) * θ := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [hv l hl, ← Finset.sum_mul]
        push_cast
        ring
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_div]
  rw [hs]
  push_cast
  ring

theorem readout_gain_ge_two
    {ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (a : ι → ℝ) (β : κ → ℝ)
    (ha : ∀ i ∈ I, 0 ≤ a i)
    (hi : ∃ i ∈ I, a i = 1) (hl : ∃ l ∈ J, β l = 1) :
    2 ≤ 2 * (∑ l ∈ J, β l ^ 2) * (∑ i ∈ I, a i) := by
  obtain ⟨i, hiI, hai⟩ := hi
  obtain ⟨l, hlJ, hβl⟩ := hl
  have hsA : 1 ≤ ∑ i ∈ I, a i := by
    simpa [hai] using Finset.single_le_sum ha hiI
  have hsB : 1 ≤ ∑ l ∈ J, β l ^ 2 := by
    simpa [hβl] using Finset.single_le_sum (fun l _ => sq_nonneg (β l)) hlJ
  nlinarith [mul_le_mul hsB hsA (by norm_num : (0 : ℝ) ≤ 1)
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) hsB)]

theorem tendsto_atTop_of_eventually_square_le
    (r : ℕ → ℝ) (N : ℕ) (hr : ∀ n, N ≤ n → 0 ≤ r n)
    (hstep : ∀ n, N ≤ n → (r n) ^ 2 ≤ r (n + 1)) (hinit : 1 < r N) :
    Filter.Tendsto r Filter.atTop Filter.atTop := by
  apply (Filter.tendsto_add_atTop_iff_nat N).1
  apply tendsto_atTop_of_square_le (fun n => r (n + N))
  · intro n
    exact hr _ (Nat.le_add_left _ _)
  · intro n
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hstep (n + N) (Nat.le_add_left _ _)
  · simpa using hinit

theorem aligned_orbit_escape
    (z : ℕ → ℂ) (c : ℕ → ℝ) (θ : ℂ)
    (hθ : ‖θ‖ = 1) (hc : ∀ n, 0 ≤ c n)
    (hinit : z 0 = (‖z 0‖ : ℂ) * θ) (hz0 : z 0 ≠ 0)
    (hstep : ∀ n, z (n + 1) = z n ^ 2 + (c n : ℂ) * θ ^ (2 ^ (n + 1)))
    (hgain : ∃ j, 2 ≤ c j) :
    Filter.Tendsto (fun n => ‖z n‖) Filter.atTop Filter.atTop := by
  obtain ⟨j, hj⟩ := hgain
  have hn := aligned_orbit_norm z c θ hθ hc hinit hz0 hstep
  apply tendsto_atTop_of_eventually_square_le (fun n => ‖z n‖) (j + 1)
  · intro n _
    exact norm_nonneg _
  · intro n _
    rw [hn n]
    exact le_add_of_nonneg_right (hc n)
  · rw [hn j]
    nlinarith [sq_nonneg ‖z j‖]

end Problem340

end

end OAI
