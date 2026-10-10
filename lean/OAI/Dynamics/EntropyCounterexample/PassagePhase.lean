import OAI.Dynamics.EntropyCounterexample.PhaseAlignment

namespace OAI

noncomputable section

namespace Problem340.PassagePhase

def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

lemma norm_phase {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  simp [phase, Complex.norm_real, norm_ne_zero_iff.mpr hz]

lemma norm_mul_phase (z : ℂ) : (‖z‖ : ℂ) * phase z = z := by
  by_cases hz : z = 0
  · simp [phase, hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    dsimp [phase]
    field_simp

theorem delayed_readout_sum
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : κ → ℝ) (v : κ → ℂ)
    (θ : ℂ) (n : ℕ)
    (hI : ∀ i ∈ I, i ≤ n)
    (hp : ∀ i ∈ I, phase (z i) = θ ^ (2 ^ i))
    (hv : ∀ l ∈ J, β l ≠ 0 → v l = ((β l / 10 : ℝ) : ℂ) *
      ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1))) :
    (20 : ℂ) * (∑ l ∈ J, (β l : ℂ) * v l) =
      ((2 * (∑ l ∈ J, β l ^ 2) * (∑ i ∈ I, w i) : ℝ) : ℂ) *
        θ ^ (2 ^ (n + 1)) := by
  let v' : κ → ℂ := fun l => ((β l / 10 : ℝ) : ℂ) *
    ∑ i ∈ I, (w i : ℂ) * θ ^ (2 ^ (n + 1))
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
      rw [hp i hi, prediction_phase_power θ i n (hI i hi)]
  rw [hs]
  exact aligned_readout_sum I J w β v' (θ ^ (2 ^ (n + 1))) (fun _ _ => rfl)

theorem readout_sum_of_preparation_phases
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : κ → ℝ) (v : κ → ℂ)
    (θ : ℂ) (K n : ℕ) (hI : ∀ i ∈ I, i < K)
    (hearly : n < K → ∀ l ∈ J, β l = 0)
    (hp : ∀ i ∈ I, i ≤ n → phase (z i) = θ ^ (2 ^ i))
    (hv : ∀ l ∈ J, β l ≠ 0 → v l = ((β l / 10 : ℝ) : ℂ) *
      ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1))) :
    (20 : ℂ) * (∑ l ∈ J, (β l : ℂ) * v l) =
      ((2 * (∑ l ∈ J, β l ^ 2) * (∑ i ∈ I, w i) : ℝ) : ℂ) *
        θ ^ (2 ^ (n + 1)) := by
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
  · have hin : ∀ i ∈ I, i ≤ n := by
      intro i hi
      have := hI i hi
      omega
    exact delayed_readout_sum I J z w β v θ n hin (fun i hi => hp i hi (hin i hi)) hv

def gain {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (n : ℕ) : ℝ :=
  2 * (∑ l ∈ J, β n l ^ 2) * (∑ i ∈ I, w i)

lemma gain_nonneg {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (w : ℕ → ℝ) (β : ℕ → κ → ℝ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (n : ℕ) : 0 ≤ gain I J w β n := by
  apply mul_nonneg
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun l _ => sq_nonneg (β n l))
  · exact Finset.sum_nonneg hw

theorem passage_phase
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (v : ℕ → κ → ℂ)
    (K N : ℕ) (hz0 : z 0 ≠ 0)
    (hI : ∀ i ∈ I, i < K) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hearly : ∀ n, n < K → ∀ l ∈ J, β n l = 0)
    (hv : ∀ n, n < N → ∀ l ∈ J, β n l ≠ 0 →
      v n l = ((β n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1)))
    (hrec : ∀ n, n < N → z (n + 1) = z n ^ 2 +
      (20 : ℂ) * (∑ l ∈ J, (β n l : ℂ) * v n l)) :
    ∀ n, n ≤ N → z n ≠ 0 ∧ phase (z n) = phase (z 0) ^ (2 ^ n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hnN
      have haligned : ∀ m, m < n → z (m + 1) = z m ^ 2 +
          (gain I J w β m : ℂ) * phase (z 0) ^ (2 ^ (m + 1)) := by
        intro m hm
        rw [hrec m (lt_of_lt_of_le hm hnN)]
        congr 1
        apply readout_sum_of_preparation_phases I J z w (β m) (v m)
          (phase (z 0)) K m hI (hearly m)
        · intro i hi him
          exact (ih i (lt_of_le_of_lt him hm) (by omega)).2
        · exact hv m (lt_of_lt_of_le hm hnN)
      have hresult := aligned_orbit_phase_until z (gain I J w β) (phase (z 0)) n
        (norm_phase hz0) (gain_nonneg I J w β hw) (norm_mul_phase (z 0)).symm
        hz0 haligned n le_rfl
      refine ⟨hresult.1, ?_⟩
      have hn : (‖z n‖ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hresult.1)
      apply mul_left_cancel₀ hn
      exact (norm_mul_phase (z n)).trans hresult.2

theorem passage_radial_step
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (v : ℕ → κ → ℂ)
    (K N : ℕ) (hz0 : z 0 ≠ 0)
    (hI : ∀ i ∈ I, i < K) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hearly : ∀ n, n < K → ∀ l ∈ J, β n l = 0)
    (hv : ∀ n, n < N → ∀ l ∈ J, β n l ≠ 0 →
      v n l = ((β n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1)))
    (hrec : ∀ n, n < N → z (n + 1) = z n ^ 2 +
      (20 : ℂ) * (∑ l ∈ J, (β n l : ℂ) * v n l)) :
    ∀ n, n < N → ‖z (n + 1)‖ = ‖z n‖ ^ 2 + gain I J w β n := by
  intro n hn
  have hp := passage_phase I J z w β v K N hz0 hI hw hearly hv hrec
  have hs := readout_sum_of_preparation_phases I J z w (β n) (v n)
    (phase (z 0)) K n hI (hearly n)
    (fun i _ hin => (hp i (by omega)).2) (hv n hn)
  have hu : ‖phase (z 0) ^ (2 ^ n)‖ = 1 := by
    rw [norm_pow, norm_phase hz0, one_pow]
  have hz : z n = (‖z n‖ : ℂ) * phase (z 0) ^ (2 ^ n) := by
    rw [← (hp n hn.le).2]
    exact (norm_mul_phase (z n)).symm
  have hpow : phase (z 0) ^ (2 ^ (n + 1)) = (phase (z 0) ^ (2 ^ n)) ^ 2 := by
    rw [pow_succ, pow_mul]
  rw [hrec n hn, hs, hpow]
  exact aligned_square_norm _ _ _ _ hu hz (norm_nonneg _) (gain_nonneg I J w β hw n)

theorem passage_contains_large_radius
    {κ : Type*} (I : Finset ℕ) (J : Finset κ)
    (z : ℕ → ℂ) (w : ℕ → ℝ) (β : ℕ → κ → ℝ) (v : ℕ → κ → ℂ)
    (K N : ℕ) (hz0 : z 0 ≠ 0)
    (hI : ∀ i ∈ I, i < K) (hw : ∀ i ∈ I, 0 ≤ w i)
    (hearly : ∀ n, n < K → ∀ l ∈ J, β n l = 0)
    (hv : ∀ n, n < N → ∀ l ∈ J, β n l ≠ 0 →
      v n l = ((β n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (w i : ℂ) * phase (z i) ^ (2 ^ (n - i + 1)))
    (hrec : ∀ n, n < N → z (n + 1) = z n ^ 2 +
      (20 : ℂ) * (∑ l ∈ J, (β n l : ℂ) * v n l))
    (hprep : ∃ i ∈ I, w i = 1)
    (hread : ∃ j, j < N ∧ ∃ l ∈ J, β j l = 1) :
    ∃ n, n ≤ N ∧ 1 < ‖z n‖ := by
  obtain ⟨j, hj, hl⟩ := hread
  refine ⟨j + 1, by omega, ?_⟩
  rw [passage_radial_step I J z w β v K N hz0 hI hw hearly hv hrec j hj]
  have hg : 2 ≤ gain I J w β j := readout_gain_ge_two I J w (β j) hw hprep hl
  nlinarith [sq_nonneg ‖z j‖]

end Problem340.PassagePhase

end

end OAI
