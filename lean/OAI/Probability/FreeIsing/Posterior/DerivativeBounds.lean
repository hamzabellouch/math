import OAI.Probability.FreeIsing.Posterior.FieldCalculus

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePosterior

variable {S : Type*} [Fintype S] [Nonempty S]

theorem abs_mean_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hbound : ∀ s, |observable s| ≤ A) :
    |mean energy signal observable t| ≤ A := by
  rw [mean_eq_sum_mass]
  calc
    |∑ s, observable s * mass energy signal t s| ≤
        ∑ s, |observable s * mass energy signal t s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, A * mass energy signal t s := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul, abs_of_pos (mass_pos energy signal t s)]
      exact mul_le_mul_of_nonneg_right (hbound s) (mass_pos energy signal t s).le
    _ = A := by rw [← Finset.mul_sum, sum_mass, mul_one]

omit [Fintype S] [Nonempty S] in
lemma abs_spin_eq_one (signal : S → ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) (s : S) : |signal s| = 1 := by
  rcases hsignal s with hs | hs <;> simp [hs]

theorem abs_mean_spin_le_one (energy signal : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) :
    |mean energy signal signal t| ≤ 1 :=
  abs_mean_le energy signal signal t 1 (fun s => (abs_spin_eq_one signal hsignal s).le)

theorem abs_tiltCovariance_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |tiltCovariance energy signal observable t| ≤ 2 * A := by
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  have hprod : ∀ s, |observable s * signal s| ≤ A := by
    intro s
    rw [abs_mul, abs_spin_eq_one signal hsignal s, mul_one]
    exact hbound s
  unfold tiltCovariance
  calc
    |mean energy signal (fun s => observable s * signal s) t -
        mean energy signal observable t * mean energy signal signal t| ≤
      |mean energy signal (fun s => observable s * signal s) t| +
        |mean energy signal observable t * mean energy signal signal t| := abs_sub _ _
    _ ≤ A + A * 1 := add_le_add (abs_mean_le energy signal _ t A hprod)
      (by
        rw [abs_mul]
        exact mul_le_mul (abs_mean_le energy signal observable t A hbound)
          (abs_mean_spin_le_one energy signal t hsignal) (abs_nonneg _) hA)
    _ = 2 * A := by ring

theorem abs_deriv_mean_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (mean energy signal observable) t| ≤ 2 * A := by
  rw [(hasDerivAt_mean_covariance energy signal observable t).deriv]
  exact abs_tiltCovariance_le energy signal observable t A hsignal hbound

theorem abs_deriv_deriv_mean_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (deriv (mean energy signal observable)) t| ≤ 4 * A := by
  rw [deriv_deriv_mean energy signal observable t hsignal, abs_mul, abs_mul]
  norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm := abs_mean_spin_le_one energy signal t hsignal
  have hc := abs_tiltCovariance_le energy signal observable t A hsignal hbound
  calc
    2 * |mean energy signal signal t| * |tiltCovariance energy signal observable t| ≤
        2 * 1 * (2 * A) := by gcongr
    _ = 4 * A := by ring

lemma deriv_mean_square (energy signal observable : S → ℝ) (t : ℝ) :
    deriv (fun u => mean energy signal observable u ^ 2) t =
      2 * mean energy signal observable t * tiltCovariance energy signal observable t := by
  have hd := (hasDerivAt_mean_covariance energy signal observable t).pow 2
  change HasDerivAt (fun u => mean energy signal observable u ^ 2) _ t at hd
  simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hd.deriv

theorem abs_deriv_mean_square_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (fun u => mean energy signal observable u ^ 2) t| ≤ 4 * A ^ 2 := by
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  rw [deriv_mean_square, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hm := abs_mean_le energy signal observable t A hbound
  have hc := abs_tiltCovariance_le energy signal observable t A hsignal hbound
  calc
    2 * |mean energy signal observable t| * |tiltCovariance energy signal observable t| ≤
      2 * A * (2 * A) := by gcongr
    _ = 4 * A ^ 2 := by ring

theorem abs_deriv_deriv_mean_square_le (energy signal observable : S → ℝ) (t A : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (deriv (fun u => mean energy signal observable u ^ 2)) t| ≤ 16 * A ^ 2 := by
  have he := mean_square_drift_cancellation energy signal observable t hsignal
  have hderiv := abs_deriv_mean_square_le energy signal observable t A hsignal hbound
  have hmean := abs_mean_spin_le_one energy signal t hsignal
  have hcov := abs_tiltCovariance_le energy signal observable t A hsignal hbound
  have hA : 0 ≤ A := (abs_nonneg (observable (Classical.arbitrary S))).trans
    (hbound (Classical.arbitrary S))
  have hsq : tiltCovariance energy signal observable t ^ 2 ≤ 4 * A ^ 2 := by
    have hs := mul_le_mul hcov hcov (abs_nonneg _) (by positivity : 0 ≤ 2 * A)
    nlinarith [sq_abs (tiltCovariance energy signal observable t)]
  have heq : deriv (deriv (fun u => mean energy signal observable u ^ 2)) t =
      2 * (tiltCovariance energy signal observable t ^ 2 -
        deriv (fun u => mean energy signal observable u ^ 2) t * mean energy signal signal t) := by
    linarith
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * |tiltCovariance energy signal observable t ^ 2 -
        deriv (fun u => mean energy signal observable u ^ 2) t * mean energy signal signal t| ≤
      2 * (|tiltCovariance energy signal observable t ^ 2| +
        |deriv (fun u => mean energy signal observable u ^ 2) t * mean energy signal signal t|) := by
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
    _ ≤ 2 * (4 * A ^ 2 + 4 * A ^ 2 * 1) := by
      rw [abs_of_nonneg (sq_nonneg _), abs_mul]
      gcongr
    _ = 16 * A ^ 2 := by ring

section Fields

variable {V : Type*} [Fintype V]

theorem abs_fieldMean_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (A : ℝ)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldMean energy spin observable x| ≤ A := by
  rw [← mean_fieldEnergy_zero energy spin (fun _ => 0)]
  exact abs_mean_le _ _ _ _ _ hbound

theorem abs_fieldCovariance_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V) (A : ℝ)
    (hcoord : ∀ s, spin s u = -1 ∨ spin s u = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldCovariance energy spin observable x u| ≤ 2 * A := by
  have h := abs_tiltCovariance_le (fieldEnergy energy spin x) (fun s => spin s u)
    observable 0 A hcoord hbound
  simpa only [tiltCovariance, mean_fieldEnergy_zero, fieldCovariance] using h

theorem abs_fieldMean_square_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (A : ℝ)
    (hbound : ∀ s, |observable s| ≤ A) :
    |fieldMean energy spin observable x ^ 2| ≤ A ^ 2 := by
  have h := abs_fieldMean_le energy spin observable x A hbound
  have hA : 0 ≤ A := (abs_nonneg _).trans h
  have hs := mul_le_mul h h (abs_nonneg _) hA
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_abs (fieldMean energy spin observable x)]

variable [DecidableEq V]

theorem abs_deriv_fieldMean_coordinate_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V) (t A : ℝ)
    (hcoord : ∀ s, spin s u = -1 ∨ spin s u = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (fun r => fieldMean energy spin observable
      (fun v => x v + if v = u then r else 0)) t| ≤ 2 * A := by
  simp_rw [fieldMean_coordinate_tilt]
  exact abs_deriv_mean_le _ _ _ _ _ hcoord hbound

theorem abs_deriv_deriv_fieldMean_coordinate_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V) (t A : ℝ)
    (hcoord : ∀ s, spin s u = -1 ∨ spin s u = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (deriv (fun r => fieldMean energy spin observable
      (fun v => x v + if v = u then r else 0))) t| ≤ 4 * A := by
  simp_rw [fieldMean_coordinate_tilt]
  exact abs_deriv_deriv_mean_le _ _ _ _ _ hcoord hbound

theorem abs_deriv_fieldMean_square_coordinate_le (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V) (t A : ℝ)
    (hcoord : ∀ s, spin s u = -1 ∨ spin s u = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (fun r => fieldMean energy spin observable
      (fun v => x v + if v = u then r else 0) ^ 2) t| ≤ 4 * A ^ 2 := by
  simp_rw [fieldMean_coordinate_tilt]
  exact abs_deriv_mean_square_le _ _ _ _ _ hcoord hbound

theorem abs_deriv_deriv_fieldMean_square_coordinate_le
    (energy : S → ℝ) (spin : S → V → ℝ) (observable : S → ℝ)
    (x : V → ℝ) (u : V) (t A : ℝ)
    (hcoord : ∀ s, spin s u = -1 ∨ spin s u = 1)
    (hbound : ∀ s, |observable s| ≤ A) :
    |deriv (deriv (fun r => fieldMean energy spin observable
      (fun v => x v + if v = u then r else 0) ^ 2)) t| ≤ 16 * A ^ 2 := by
  simp_rw [fieldMean_coordinate_tilt]
  exact abs_deriv_deriv_mean_square_le _ _ _ _ _ hcoord hbound

end Fields

end Problem367.FinitePosterior

end

end OAI
