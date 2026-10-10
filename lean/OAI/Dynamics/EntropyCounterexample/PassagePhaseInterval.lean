import OAI.Dynamics.EntropyCounterexample.PassagePhase

namespace OAI

noncomputable section

namespace Problem340.PassagePhase

theorem prediction_phase_power_from (θ : ℂ) (s i n : ℕ) (hsi : s ≤ i) (hin : i ≤ n) :
    (θ ^ (2 ^ (i - s))) ^ (2 ^ (n - i + 1)) = θ ^ (2 ^ (n - s + 1)) := by
  rw [← pow_mul, ← pow_add]
  congr 2
  omega

theorem delayed_readout_sum_from
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : κ → ℝ) (v : κ → ℂ)
    (θ : ℂ) (s n : ℕ)
    (hI : ∀ i ∈ I, s ≤ i ∧ i ≤ n)
    (hp : ∀ i ∈ I, phase (z i) = θ ^ (2 ^ (i - s)))
    (hv : ∀ l ∈ J, β l ≠ 0 → v l = ((β l / 10 : ℝ) : ℂ) *
      ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1))) :
    (20 : ℂ) * (∑ l ∈ J, (β l : ℂ) * v l) =
      ((2 * (∑ l ∈ J, β l ^ 2) * (∑ i ∈ I, w i) : ℝ) : ℂ) *
        θ ^ (2 ^ (n - s + 1)) := by
  let v' : κ → ℂ := fun l => ((β l / 10 : ℝ) : ℂ) *
    ∑ i ∈ I, (w i : ℂ) * θ ^ (2 ^ (n - s + 1))
  have hs : (∑ l ∈ J, (β l : ℂ) * v l) =
      ∑ l ∈ J, (β l : ℂ) * v' l := by
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hb : β l = 0
    · simp [hb]
    · rw [hv l hl hb]
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      rw [hp i hi, prediction_phase_power_from θ s i n (hI i hi).1 (hI i hi).2]
  rw [hs]
  exact aligned_readout_sum I J w β v' (θ ^ (2 ^ (n - s + 1))) (fun _ _ => rfl)

theorem readout_sum_of_preparation_phases_from
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : κ → ℝ) (v : κ → ℂ)
    (θ : ℂ) (s K n : ℕ) (hI : ∀ i ∈ I, s ≤ i ∧ i < K)
    (hearly : n < K → ∀ l ∈ J, β l = 0)
    (hp : ∀ i ∈ I, i ≤ n → phase (z i) = θ ^ (2 ^ (i - s)))
    (hv : ∀ l ∈ J, β l ≠ 0 → v l = ((β l / 10 : ℝ) : ℂ) *
      ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1))) :
    (20 : ℂ) * (∑ l ∈ J, (β l : ℂ) * v l) =
      ((2 * (∑ l ∈ J, β l ^ 2) * (∑ i ∈ I, w i) : ℝ) : ℂ) *
        θ ^ (2 ^ (n - s + 1)) := by
  by_cases hnK : n < K
  · have hb : ∀ l ∈ J, β l = 0 := hearly hnK
    have hs : (∑ l ∈ J, (β l : ℂ) * v l) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      simp [hb l hl]
    have hb2 : (∑ l ∈ J, β l ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      simp [hb l hl]
    simp [hs, hb2]
  · have hin : ∀ i ∈ I, s ≤ i ∧ i ≤ n := by
      intro i hi
      have := hI i hi
      omega
    exact delayed_readout_sum_from I J z w β v θ s n hin
      (fun i hi => hp i hi (hin i hi).2) hv

theorem passage_phase_interval
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (v : ℕ → κ → ℂ)
    (s K N : ℕ) (hzs : z s ≠ 0)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l ∈ J, β n l = 0)
    (hv : ∀ n, s ≤ n → n < N → ∀ l ∈ J, β n l ≠ 0 →
      v n l = ((β n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1)))
    (hrec : ∀ n, s ≤ n → n < N → z (n + 1) = z n ^ 2 +
      (20 : ℂ) * (∑ l ∈ J, (β n l : ℂ) * v n l)) :
    ∀ n, s ≤ n → n ≤ N →
      z n ≠ 0 ∧ phase (z n) = phase (z s) ^ (2 ^ (n - s)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hsn hnN
      have haligned : ∀ m, m < n - s → z (s + (m + 1)) = z (s + m) ^ 2 +
          (gain I J w β (s + m) : ℂ) * phase (z s) ^ (2 ^ (m + 1)) := by
        intro m hm
        have hsm : s ≤ s + m := by omega
        have hmn : s + m < n := by omega
        have hs := readout_sum_of_preparation_phases_from I J z w (β (s + m))
          (v (s + m)) (phase (z s)) s K (s + m) hI (hearly (s + m) hsm)
          (fun i hi him => (ih i (by omega) (hI i hi).1 (by omega)).2)
          (hv (s + m) hsm (by omega))
        rw [show s + (m + 1) = s + m + 1 by omega, hrec (s + m) hsm (by omega)]
        congr 1
        simpa only [gain, Nat.add_sub_cancel_left] using hs
      have hresult := aligned_orbit_phase_until (fun m => z (s + m))
        (fun m => gain I J w β (s + m)) (phase (z s)) (n - s)
        (norm_phase hzs) (fun m => gain_nonneg I J w β hw (s + m))
        (by simpa using (norm_mul_phase (z s)).symm) (by simpa using hzs)
        haligned (n - s) le_rfl
      have hr : z n ≠ 0 ∧ z n = (‖z n‖ : ℂ) * phase (z s) ^ (2 ^ (n - s)) := by
        simpa only [Nat.add_sub_of_le hsn] using hresult
      refine ⟨hr.1, ?_⟩
      have hn : (‖z n‖ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hr.1)
      apply mul_left_cancel₀ hn
      exact (norm_mul_phase (z n)).trans hr.2

theorem passage_radial_step_interval
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (v : ℕ → κ → ℂ)
    (s K N : ℕ) (hzs : z s ≠ 0)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l ∈ J, β n l = 0)
    (hv : ∀ n, s ≤ n → n < N → ∀ l ∈ J, β n l ≠ 0 →
      v n l = ((β n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1)))
    (hrec : ∀ n, s ≤ n → n < N → z (n + 1) = z n ^ 2 +
      (20 : ℂ) * (∑ l ∈ J, (β n l : ℂ) * v n l)) :
    ∀ n, s ≤ n → n < N → ‖z (n + 1)‖ = ‖z n‖ ^ 2 + gain I J w β n := by
  intro n hsn hn
  have hp := passage_phase_interval I J z w β v s K N hzs hI hw hearly hv hrec
  have hs := readout_sum_of_preparation_phases_from I J z w (β n) (v n)
    (phase (z s)) s K n hI (hearly n hsn)
    (fun i hi hin => (hp i (hI i hi).1 (by omega)).2) (hv n hsn hn)
  have hu : ‖phase (z s) ^ (2 ^ (n - s))‖ = 1 := by
    rw [norm_pow, norm_phase hzs, one_pow]
  have hz : z n = (‖z n‖ : ℂ) * phase (z s) ^ (2 ^ (n - s)) := by
    rw [← (hp n hsn hn.le).2]
    exact (norm_mul_phase (z n)).symm
  have hpow : phase (z s) ^ (2 ^ (n - s + 1)) = (phase (z s) ^ (2 ^ (n - s))) ^ 2 := by
    rw [pow_succ, pow_mul]
  rw [hrec n hsn hn, hs, hpow]
  exact aligned_square_norm _ _ _ _ hu hz (norm_nonneg _) (gain_nonneg I J w β hw n)

theorem passage_square_le_interval
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (v : ℕ → κ → ℂ)
    (s K N : ℕ) (hzs : z s ≠ 0)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l ∈ J, β n l = 0)
    (hv : ∀ n, s ≤ n → n < N → ∀ l ∈ J, β n l ≠ 0 →
      v n l = ((β n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1)))
    (hrec : ∀ n, s ≤ n → n < N → z (n + 1) = z n ^ 2 +
      (20 : ℂ) * (∑ l ∈ J, (β n l : ℂ) * v n l)) :
    ∀ n, s ≤ n → n < N → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖ := by
  intro n hsn hn
  rw [passage_radial_step_interval I J z w β v s K N hzs hI hw hearly hv hrec n hsn hn]
  exact le_add_of_nonneg_right (gain_nonneg I J w β hw n)

theorem passage_contains_large_radius_interval
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (v : ℕ → κ → ℂ)
    (s K N : ℕ) (hzs : z s ≠ 0)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l ∈ J, β n l = 0)
    (hv : ∀ n, s ≤ n → n < N → ∀ l ∈ J, β n l ≠ 0 →
      v n l = ((β n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1)))
    (hrec : ∀ n, s ≤ n → n < N → z (n + 1) = z n ^ 2 +
      (20 : ℂ) * (∑ l ∈ J, (β n l : ℂ) * v n l))
    (hprep : ∃ i ∈ I, w i = 1)
    (hread : ∃ j, s ≤ j ∧ j < N ∧ ∃ l ∈ J, β j l = 1) :
    ∃ n, s ≤ n ∧ n ≤ N ∧ 1 < ‖z n‖ := by
  obtain ⟨j, hsj, hj, hl⟩ := hread
  refine ⟨j + 1, by omega, by omega, ?_⟩
  rw [passage_radial_step_interval I J z w β v s K N hzs hI hw hearly hv hrec j hsj hj]
  have hg : 2 ≤ gain I J w β j := readout_gain_ge_two I J w (β j) hw hprep hl
  nlinarith [sq_nonneg ‖z j‖]

theorem passage_escape_of_preparation_plateau
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (v : ℕ → κ → ℂ)
    (s K N : ℕ) (hzs : z s ≠ 0)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l ∈ J, β n l = 0)
    (hv : ∀ n, s ≤ n → n < N → ∀ l ∈ J, β n l ≠ 0 →
      v n l = ((β n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1)))
    (hrec : ∀ n, s ≤ n → n < N → z (n + 1) = z n ^ 2 +
      (20 : ℂ) * (∑ l ∈ J, (β n l : ℂ) * v n l))
    (a : ℕ → ℝ) (χ : ℂ → ℝ) (hKN : K ≤ N)
    (hweight : ∀ i ∈ I, w i = a i * χ (z i))
    (hhalf : ∀ i ∈ I, (1 / 2 : ℝ) < ‖z i‖)
    (hcutoff : ∀ u : ℂ, (1 / 2 : ℝ) ≤ ‖u‖ → ‖u‖ ≤ 1 → χ u = 1)
    (hprep : ∃ i ∈ I, a i = 1)
    (hread : ∃ j, s ≤ j ∧ j < N ∧ ∃ l ∈ J, β j l = 1) :
    ∃ n, s ≤ n ∧ n ≤ N ∧ 1 < ‖z n‖ := by
  obtain ⟨i, hi, hai⟩ := hprep
  by_cases hlarge : 1 < ‖z i‖
  · exact ⟨i, (hI i hi).1, le_trans (hI i hi).2.le hKN, hlarge⟩
  · have hwi : w i = 1 := by
      rw [hweight i hi, hai, hcutoff (z i) (hhalf i hi).le (le_of_not_gt hlarge)]
      simp
    exact passage_contains_large_radius_interval I J z w β v s K N hzs hI hw
      hearly hv hrec ⟨i, hi, hwi⟩ hread

end Problem340.PassagePhase

end

end OAI
