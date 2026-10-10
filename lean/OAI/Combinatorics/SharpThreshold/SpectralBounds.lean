import Mathlib

namespace OAI

universe u

noncomputable section

namespace Problem313

/-- A finite spectral tail is controlled by its first degree moment. -/
theorem finite_spectral_tail {ι : Type u} (s : Finset ι)
    (mass degree : ι → ℝ) (cutoff : ℝ) (hcutoff : 0 < cutoff)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hdegree : ∀ i ∈ s, 0 ≤ degree i) :
    (∑ i ∈ s with cutoff < degree i, mass i) ≤
      (∑ i ∈ s, degree i * mass i) / cutoff := by
  classical
  apply (le_div_iff₀ hcutoff).2
  rw [Finset.sum_mul]
  calc
    ∑ i ∈ s with cutoff < degree i, mass i * cutoff ≤
        ∑ i ∈ s with cutoff < degree i, degree i * mass i := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨his, hiq⟩ := Finset.mem_filter.mp hi
      nlinarith [hmass i his]
    _ ≤ ∑ i ∈ s, degree i * mass i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i hi _
      exact mul_nonneg (hdegree i hi) (hmass i hi)

/-- Splitting at a positive spectral cutoff gives a low-degree term and a tail. -/
theorem finite_spectral_split {ι : Type u} (s : Finset ι)
    (mass degree : ι → ℝ) (cutoff : ℝ) (hcutoff : 0 < cutoff)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hdegree : ∀ i ∈ s, 0 ≤ degree i) :
    (∑ i ∈ s, mass i) ≤
      (∑ i ∈ s with degree i ≤ cutoff, mass i) +
      (∑ i ∈ s, degree i * mass i) / cutoff := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun i => degree i ≤ cutoff) mass
  simp only [not_le] at hsplit
  rw [← hsplit]
  exact add_le_add le_rfl (finite_spectral_tail s mass degree cutoff hcutoff hmass hdegree)

/-- The bias cancels exactly in the tail term at the bias-dependent cutoff. -/
theorem variance_tail_bias_cancellation (sigma ell : ℝ)
    (hsigma : sigma ≠ 0) (hell : ell ≠ 0) :
    sigma ^ 2 / ((sigma * ell / 64) ^ 2 / 2) = 8192 / ell ^ 2 := by
  field_simp
  ring

/-- Assemble low-degree capture and the Dirichlet identity into a variance bound. -/
theorem variance_from_spectral_capture {ι : Type u} (s : Finset ι)
    (mass degree : ι → ℝ) (sigma ell influence lowConstant : ℝ)
    (hsigma : 0 < sigma) (hell : 0 < ell)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hdegree : ∀ i ∈ s, 0 ≤ degree i)
    (hcapture : (∑ i ∈ s with degree i ≤ (sigma * ell / 64) ^ 2 / 2, mass i)
      ≤ lowConstant * influence)
    (hdirichlet : (∑ i ∈ s, degree i * mass i) = sigma ^ 2 * influence) :
    (∑ i ∈ s, mass i) ≤ (lowConstant + 8192 / ell ^ 2) * influence := by
  have hcutoff : 0 < (sigma * ell / 64) ^ 2 / 2 := by positivity
  have hsplit := finite_spectral_split s mass degree _ hcutoff hmass hdegree
  have htail : sigma ^ 2 * influence / ((sigma * ell / 64) ^ 2 / 2) =
      (8192 / ell ^ 2) * influence := by
    calc
      _ = (sigma ^ 2 / ((sigma * ell / 64) ^ 2 / 2)) * influence := by ring
      _ = _ := by rw [variance_tail_bias_cancellation sigma ell hsigma.ne' hell.ne']
  rw [hdirichlet, htail] at hsplit
  nlinarith

/-- The two numerical terms fit inside the advertised universal constant. -/
theorem variance_constant_assembly (t ell lowConstant : ℝ)
    (ht : 0 < t) (hell : t / 3 ≤ ell)
    (hlow : lowConstant ≤ 256 / t ^ 2) :
    lowConstant + 8192 / ell ^ 2 ≤ (2 : ℝ) ^ 17 / t ^ 2 := by
  have hellpos : 0 < ell := lt_of_lt_of_le (by positivity : 0 < t / 3) hell
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ t / 3) hell
  have htail : 8192 / ell ^ 2 ≤ 73728 / t ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hellpos) (sq_pos_of_pos ht)).2
    nlinarith
  have hbudget : 256 / t ^ 2 + 73728 / t ^ 2 ≤ (2 : ℝ) ^ 17 / t ^ 2 := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right
    · norm_num
    · positivity
  linarith

/-- A more flexible numerical budget, useful with coarse exponential estimates. -/
theorem variance_constant_assembly_budget (t ell lowConstant budget : ℝ)
    (ht : 0 < t) (hell : t / 3 ≤ ell)
    (hlow : lowConstant ≤ budget / t ^ 2)
    (hbudget : budget + 73728 ≤ (2 : ℝ) ^ 17) :
    lowConstant + 8192 / ell ^ 2 ≤ (2 : ℝ) ^ 17 / t ^ 2 := by
  have hellpos : 0 < ell := lt_of_lt_of_le (by positivity : 0 < t / 3) hell
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ t / 3) hell
  have htail : 8192 / ell ^ 2 ≤ 73728 / t ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hellpos) (sq_pos_of_pos ht)).2
    nlinarith
  calc
    lowConstant + 8192 / ell ^ 2 ≤ budget / t ^ 2 + 73728 / t ^ 2 :=
      add_le_add hlow htail
    _ = (budget + 73728) / t ^ 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hbudget (sq_nonneg t)

/-- A small logarithm only needs the elementary Poincaré bound. -/
theorem variance_small_log_assembly (t variance influence : ℝ)
    (ht : 0 < t) (htsmall : t ≤ 16) (hinfluence : 0 ≤ influence)
    (hpoincare : variance ≤ influence / 4) :
    variance ≤ ((2 : ℝ) ^ 17 / t ^ 2) * influence := by
  have hsq : t ^ 2 ≤ 256 := by nlinarith
  have hfactor : (1 / 4 : ℝ) ≤ (2 : ℝ) ^ 17 / t ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos ht)).2
    norm_num
    nlinarith
  calc
    variance ≤ (1 / 4 : ℝ) * influence := by linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hinfluence

/-- Final algebraic combination, leaving only the graph-specific spectral input. -/
theorem variance_large_log_assembly (t ell variance influence lowConstant : ℝ)
    (ht : 0 < t) (hell : t / 3 ≤ ell) (hinfluence : 0 ≤ influence)
    (hlow : lowConstant ≤ 256 / t ^ 2)
    (hvariance : variance ≤ (lowConstant + 8192 / ell ^ 2) * influence) :
    variance ≤ ((2 : ℝ) ^ 17 / t ^ 2) * influence :=
  hvariance.trans (mul_le_mul_of_nonneg_right
    (variance_constant_assembly t ell lowConstant ht hell hlow) hinfluence)

/-- The spectral variance bound for Fourier coefficients indexed by finite supports. -/
theorem variance_from_fourier_capture {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance sigma ell influence lowConstant : ℝ)
    (hsigma : 0 < sigma) (hell : 0 < ell)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence)
    (hcapture : (∑ S : Finset ι with S.Nonempty ∧
        (S.card : ℝ) ≤ (sigma * ell / 64) ^ 2 / 2, coeff S ^ 2)
      ≤ lowConstant * influence) :
    variance ≤ (lowConstant + 8192 / ell ^ 2) * influence := by
  classical
  let s : Finset (Finset ι) := Finset.univ.filter Finset.Nonempty
  have hdir : (∑ S ∈ s, (S.card : ℝ) * coeff S ^ 2) = sigma ^ 2 * influence := by
    rw [← hdirichlet]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S _ hS
    have hSempty : S = ∅ := by simpa [s, Finset.not_nonempty_iff_eq_empty] using hS
    simp [hSempty]
  have hcap : (∑ S ∈ s with (S.card : ℝ) ≤ (sigma * ell / 64) ^ 2 / 2, coeff S ^ 2)
      ≤ lowConstant * influence := by
    simpa only [s, Finset.filter_filter] using hcapture
  rw [hvariance]
  exact variance_from_spectral_capture s (fun S => coeff S ^ 2)
    (fun S => (S.card : ℝ)) sigma ell influence lowConstant hsigma hell
    (fun S _ => sq_nonneg _) (fun S _ => Nat.cast_nonneg _) hcap hdir

/-- Parseval and the first spectral moment immediately imply Poincaré. -/
theorem variance_le_dirichlet_of_fourier {ι : Type u} [Fintype ι] [DecidableEq ι]
    (coeff : Finset ι → ℝ) (variance dirichlet : ℝ)
    (hvariance : variance = ∑ S : Finset ι with S.Nonempty, coeff S ^ 2)
    (hdirichlet : (∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2) = dirichlet) :
    variance ≤ dirichlet := by
  classical
  rw [hvariance, ← hdirichlet]
  calc
    (∑ S : Finset ι with S.Nonempty, coeff S ^ 2) ≤
        ∑ S : Finset ι with S.Nonempty, (S.card : ℝ) * coeff S ^ 2 := by
      apply Finset.sum_le_sum
      intro S hS
      have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.mem_filter.mp hS).2
      have hcard : (1 : ℝ) ≤ S.card := by exact_mod_cast hpos
      nlinarith [sq_nonneg (coeff S)]
    _ ≤ ∑ S : Finset ι, (S.card : ℝ) * coeff S ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro S _ _
      exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

end Problem313

end

end OAI
