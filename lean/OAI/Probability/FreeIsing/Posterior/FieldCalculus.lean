import OAI.Probability.FreeIsing.Estimates.MessageFunction
import OAI.Probability.FreeIsing.Posterior.Fields
import OAI.Probability.FreeIsing.Posterior.Smooth

namespace OAI

noncomputable section

open scoped BigOperators ContDiff

namespace Problem367.FinitePosterior

variable {S : Type*} [Fintype S] [Nonempty S]

def tiltCovariance (energy signal observable : S → ℝ) (t : ℝ) : ℝ :=
  mean energy signal (fun s => observable s * signal s) t -
    mean energy signal observable t * mean energy signal signal t

def tiltField (energy signal observable : S → ℝ) (t : ℝ) : ℝ :=
  Real.artanh (mean energy signal observable t)

def tiltResponse (energy signal observable : S → ℝ) (t : ℝ) : ℝ :=
  tiltCovariance energy signal observable t /
    (1 - mean energy signal observable t ^ 2)

lemma spin_mean_variance_pos (energy signal observable : S → ℝ) (t : ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    0 < 1 - mean energy signal observable t ^ 2 := by
  have h := spin_mean_mem_Ioo energy signal observable t hspin hneg hpos
  nlinarith [h.1, h.2]

theorem hasDerivAt_mean_covariance (energy signal observable : S → ℝ) (t : ℝ) :
    HasDerivAt (mean energy signal observable)
      (tiltCovariance energy signal observable t) t :=
  hasDerivAt_mean energy signal observable t

theorem hasDerivAt_tiltCovariance (energy signal observable : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) :
    HasDerivAt (tiltCovariance energy signal observable)
      (-2 * mean energy signal signal t * tiltCovariance energy signal observable t) t := by
  have hprod : (fun s => (observable s * signal s) * signal s) = observable := by
    funext s
    rcases hsignal s with hs | hs <;> simp [hs]
  have hc := hasDerivAt_mean energy signal (fun s => observable s * signal s) t
  rw [hprod] at hc
  have hm := hasDerivAt_mean energy signal observable t
  have hn := hasDerivAt_spin_mean energy signal t hsignal
  have hd := hc.sub (hm.mul hn)
  change HasDerivAt (tiltCovariance energy signal observable) _ t at hd
  apply hd.congr_deriv
  unfold tiltCovariance
  ring

theorem deriv_deriv_mean (energy signal observable : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) :
    deriv (deriv (mean energy signal observable)) t =
      -2 * mean energy signal signal t * tiltCovariance energy signal observable t := by
  have hfun : deriv (mean energy signal observable) = tiltCovariance energy signal observable :=
    funext fun u => (hasDerivAt_mean_covariance energy signal observable u).deriv
  rw [hfun]
  exact (hasDerivAt_tiltCovariance energy signal observable t hsignal).deriv

theorem mean_drift_cancellation (energy signal observable : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) :
    deriv (mean energy signal observable) t * mean energy signal signal t +
      (1 / 2 : ℝ) * deriv (deriv (mean energy signal observable)) t = 0 := by
  rw [(hasDerivAt_mean_covariance energy signal observable t).deriv,
    deriv_deriv_mean energy signal observable t hsignal]
  ring

theorem mean_square_drift_cancellation (energy signal observable : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1) :
    deriv (fun u => mean energy signal observable u ^ 2) t * mean energy signal signal t +
      (1 / 2 : ℝ) * deriv (deriv (fun u => mean energy signal observable u ^ 2)) t =
        tiltCovariance energy signal observable t ^ 2 := by
  have hfun : deriv (fun u => mean energy signal observable u ^ 2) =
      (fun u => 2 * mean energy signal observable u * tiltCovariance energy signal observable u) := by
    funext u
    have hd := (hasDerivAt_mean_covariance energy signal observable u).pow 2
    change HasDerivAt (fun u => mean energy signal observable u ^ 2) _ u at hd
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using hd.deriv
  rw [hfun]
  have hd := ((hasDerivAt_mean_covariance energy signal observable t).const_mul 2).mul
    (hasDerivAt_tiltCovariance energy signal observable t hsignal)
  change HasDerivAt (fun u => 2 * mean energy signal observable u *
    tiltCovariance energy signal observable u) _ t at hd
  rw [hd.deriv]
  ring

theorem hasDerivAt_tiltField (energy signal observable : S → ℝ) (t : ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    HasDerivAt (tiltField energy signal observable)
      (tiltResponse energy signal observable t) t := by
  have ha := Problem367.hasDerivAt_artanh_interval
    (spin_mean_mem_Ioo energy signal observable t hspin hneg hpos)
  have hd := ha.comp t (hasDerivAt_mean_covariance energy signal observable t)
  change HasDerivAt (tiltField energy signal observable) _ t at hd
  apply hd.congr_deriv
  unfold tiltResponse
  ring

theorem hasDerivAt_tiltResponse (energy signal observable : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    HasDerivAt (tiltResponse energy signal observable)
      (-2 * mean energy signal signal t * tiltResponse energy signal observable t +
        2 * mean energy signal observable t * tiltResponse energy signal observable t ^ 2) t := by
  have hden := ne_of_gt (spin_mean_variance_pos energy signal observable t hspin hneg hpos)
  have hd := (hasDerivAt_tiltCovariance energy signal observable t hsignal).div
    (((hasDerivAt_mean_covariance energy signal observable t).pow 2).const_sub 1) hden
  change HasDerivAt (tiltResponse energy signal observable) _ t at hd
  apply hd.congr_deriv
  unfold tiltResponse
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hden]
  ring

theorem deriv_tiltField (energy signal observable : S → ℝ) (t : ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    deriv (tiltField energy signal observable) t = tiltResponse energy signal observable t :=
  (hasDerivAt_tiltField energy signal observable t hspin hneg hpos).deriv

theorem deriv_deriv_tiltField (energy signal observable : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    deriv (deriv (tiltField energy signal observable)) t =
      -2 * mean energy signal signal t * tiltResponse energy signal observable t +
        2 * mean energy signal observable t * tiltResponse energy signal observable t ^ 2 := by
  have hfun : deriv (tiltField energy signal observable) = tiltResponse energy signal observable :=
    funext fun u => deriv_tiltField energy signal observable u hspin hneg hpos
  rw [hfun]
  exact (hasDerivAt_tiltResponse energy signal observable t hsignal hspin hneg hpos).deriv

theorem tiltField_drift_cancellation (energy signal observable : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    deriv (tiltField energy signal observable) t * mean energy signal signal t +
      (1 / 2 : ℝ) * deriv (deriv (tiltField energy signal observable)) t =
        mean energy signal observable t * tiltResponse energy signal observable t ^ 2 := by
  rw [deriv_tiltField energy signal observable t hspin hneg hpos,
    deriv_deriv_tiltField energy signal observable t hsignal hspin hneg hpos]
  ring

section Fields

variable {V : Type*} [Fintype V]

def fieldCovariance (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) : ℝ :=
  fieldMean energy spin (fun s => observable s * spin s v) x -
    fieldMean energy spin observable x * fieldMean energy spin (fun s => spin s v) x

omit [Nonempty S] in
lemma fieldMean_sum_mul (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : V → S → ℝ) (a : V → ℝ) (x : V → ℝ) :
    fieldMean energy spin (fun s => ∑ v, a v * observable v s) x =
      ∑ v, a v * fieldMean energy spin (observable v) x := by
  unfold fieldMean
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_div, Finset.mul_sum, mul_div_assoc, mul_assoc]

theorem differentiable_fieldMean (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) : Differentiable ℝ (fieldMean energy spin observable) :=
  (contDiff_fieldMean_all energy spin observable 1).differentiable (by norm_num)

theorem contDiff_fieldMean_everyOrder (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (n : ℕ∞ω) : ContDiff ℝ n (fieldMean energy spin observable) :=
  contDiff_fieldMean_all energy spin observable n

theorem fderiv_fieldMean_covariance_apply (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x direction : V → ℝ) :
    fderiv ℝ (fieldMean energy spin observable) x direction =
      ∑ v, direction v * fieldCovariance energy spin observable x v := by
  rw [fderiv_fieldMean_apply]
  have hobs : (fun s => observable s * ∑ v, direction v * spin s v) =
      (fun s => ∑ v, direction v * (observable s * spin s v)) := by
    funext s
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hobs, fieldMean_sum_mul, fieldMean_sum_mul]
  simp only [fieldCovariance, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v _
  ring

def fieldMeanDerivative (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) : (V → ℝ) →L[ℝ] ℝ :=
  ∑ v, fieldCovariance energy spin observable x v • ContinuousLinearMap.proj v

theorem hasFDerivAt_fieldMean (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) :
    HasFDerivAt (fieldMean energy spin observable)
      (fieldMeanDerivative energy spin observable x) x := by
  have heq : fderiv ℝ (fieldMean energy spin observable) x =
      fieldMeanDerivative energy spin observable x := by
    ext direction
    rw [fderiv_fieldMean_covariance_apply]
    simp only [fieldMeanDerivative, sum_apply,
      smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [← heq]
  exact (differentiable_fieldMean energy spin observable x).hasFDerivAt

def fieldField (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) : ℝ :=
  Real.artanh (fieldMean energy spin observable x)

def normalizedFieldCovariance (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (v : V) : ℝ :=
  fieldCovariance energy spin observable x v /
    (1 - fieldMean energy spin observable x ^ 2)

theorem contDiff_fieldField (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (n : ℕ∞ω)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    ContDiff ℝ n (fieldField energy spin observable) := by
  have hm := contDiff_fieldMean_everyOrder energy spin observable n
  have hb (x : V → ℝ) := fieldMean_spin_mem_Ioo energy spin observable x hspin hneg hpos
  have hp (x : V → ℝ) : 0 < 1 + fieldMean energy spin observable x := by
    linarith [(hb x).1]
  have hn (x : V → ℝ) : 0 < 1 - fieldMean energy spin observable x := by
    linarith [(hb x).2]
  have hr (x : V → ℝ) : 0 < (1 + fieldMean energy spin observable x) /
      (1 - fieldMean energy spin observable x) := div_pos (hp x) (hn x)
  unfold fieldField Real.artanh
  apply ContDiff.log
  · apply ContDiff.sqrt
    · exact (contDiff_const.add hm).div (contDiff_const.sub hm) (fun x => (hn x).ne')
    · exact fun x => (hr x).ne'
  · exact fun x => (Real.sqrt_pos.mpr (hr x)).ne'

theorem hasFDerivAt_fieldField (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    HasFDerivAt (fieldField energy spin observable)
      ((1 / (1 - fieldMean energy spin observable x ^ 2)) •
        fieldMeanDerivative energy spin observable x) x := by
  exact (Problem367.hasDerivAt_artanh_interval
    (fieldMean_spin_mem_Ioo energy spin observable x hspin hneg hpos)).comp_hasFDerivAt x
      (hasFDerivAt_fieldMean energy spin observable x)

theorem fderiv_fieldField_apply (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x direction : V → ℝ)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    fderiv ℝ (fieldField energy spin observable) x direction =
      ∑ v, direction v * normalizedFieldCovariance energy spin observable x v := by
  rw [(hasFDerivAt_fieldField energy spin observable x hspin hneg hpos).fderiv]
  simp only [fieldMeanDerivative, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    normalizedFieldCovariance, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

variable [DecidableEq V]

omit [Nonempty S] in
lemma fieldMean_coordinate_tilt (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V) (t : ℝ) :
    fieldMean energy spin observable (fun v => x v + if v = u then t else 0) =
      mean (fieldEnergy energy spin x) (fun s => spin s u) observable t := by
  simpa only [mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
    fieldMean_along_line energy spin observable x (fun v => if v = u then 1 else 0) t

omit [Nonempty S] in
lemma fieldField_coordinate_tilt (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V) :
    (fun t => fieldField energy spin observable (fun v => x v + if v = u then t else 0)) =
      tiltField (fieldEnergy energy spin x) (fun s => spin s u) observable := by
  funext t
  exact congrArg Real.artanh (fieldMean_coordinate_tilt energy spin observable x u t)

omit [Nonempty S] [DecidableEq V] in
lemma tiltResponse_fieldEnergy_zero (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V) :
    tiltResponse (fieldEnergy energy spin x) (fun s => spin s u) observable 0 =
      normalizedFieldCovariance energy spin observable x u := by
  simp only [tiltResponse, tiltCovariance, mean_fieldEnergy_zero,
    normalizedFieldCovariance, fieldCovariance]

theorem fieldMean_drift_cancellation (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hcoords : ∀ s u, spin s u = -1 ∨ spin s u = 1) :
    (∑ u, deriv (fun t => fieldMean energy spin observable
        (fun v => x v + if v = u then t else 0)) 0 * fieldMean energy spin (fun s => spin s u) x) +
      (1 / 2 : ℝ) * ∑ u, deriv (deriv (fun t => fieldMean energy spin observable
        (fun v => x v + if v = u then t else 0))) 0 = 0 := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro u _
  simp_rw [fieldMean_coordinate_tilt]
  simpa only [mean_fieldEnergy_zero] using
    mean_drift_cancellation (fieldEnergy energy spin x) (fun s => spin s u) observable 0
      (fun s => hcoords s u)

theorem fieldMean_square_energy_identity (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hcoords : ∀ s u, spin s u = -1 ∨ spin s u = 1) :
    (∑ u, deriv (fun t => fieldMean energy spin observable
        (fun v => x v + if v = u then t else 0) ^ 2) 0 * fieldMean energy spin (fun s => spin s u) x) +
      (1 / 2 : ℝ) * ∑ u, deriv (deriv (fun t => fieldMean energy spin observable
        (fun v => x v + if v = u then t else 0) ^ 2)) 0 =
      ∑ u, fieldCovariance energy spin observable x u ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  simp_rw [fieldMean_coordinate_tilt]
  simpa only [mean_fieldEnergy_zero, tiltCovariance, fieldCovariance] using
    mean_square_drift_cancellation (fieldEnergy energy spin x) (fun s => spin s u) observable 0
      (fun s => hcoords s u)

theorem deriv_deriv_fieldField_coordinate (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (u : V)
    (hcoord : ∀ s, spin s u = -1 ∨ spin s u = 1)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    deriv (deriv (fun t => fieldField energy spin observable
      (fun v => x v + if v = u then t else 0))) 0 =
        -2 * fieldMean energy spin (fun s => spin s u) x * normalizedFieldCovariance energy spin observable x u +
          2 * fieldMean energy spin observable x * normalizedFieldCovariance energy spin observable x u ^ 2 := by
  rw [fieldField_coordinate_tilt]
  simpa only [mean_fieldEnergy_zero, tiltResponse_fieldEnergy_zero] using
    deriv_deriv_tiltField (fieldEnergy energy spin x) (fun s => spin s u) observable 0
      hcoord hspin hneg hpos

theorem fieldField_drift_cancellation (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ)
    (hcoords : ∀ s u, spin s u = -1 ∨ spin s u = 1)
    (hspin : ∀ s, observable s = -1 ∨ observable s = 1)
    (hneg : ∃ s, observable s = -1) (hpos : ∃ s, observable s = 1) :
    (∑ u, deriv (fun t => fieldField energy spin observable
        (fun v => x v + if v = u then t else 0)) 0 * fieldMean energy spin (fun s => spin s u) x) +
      (1 / 2 : ℝ) * ∑ u, deriv (deriv (fun t => fieldField energy spin observable
        (fun v => x v + if v = u then t else 0))) 0 =
      fieldMean energy spin observable x * ∑ u, normalizedFieldCovariance energy spin observable x u ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [fieldField_coordinate_tilt]
  simpa only [mean_fieldEnergy_zero, tiltResponse_fieldEnergy_zero] using
    tiltField_drift_cancellation (fieldEnergy energy spin x) (fun s => spin s u) observable 0
      (fun s => hcoords s u) hspin hneg hpos

end Fields

end Problem367.FinitePosterior

end

end OAI
