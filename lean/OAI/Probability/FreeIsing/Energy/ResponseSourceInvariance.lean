import OAI.Probability.FreeIsing.Posterior.FieldCalculus

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem367.FinitePosterior

variable {S : Type*} [Fintype S] [Nonempty S]

def sourceResponse (energy signal observable : S → ℝ) (t : ℝ) : ℝ :=
  tiltCovariance energy signal observable t /
    (1 - mean energy signal signal t ^ 2)

theorem hasDerivAt_sourceResponse (energy signal observable : S → ℝ) (t : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hneg : ∃ s, signal s = -1) (hpos : ∃ s, signal s = 1) :
    HasDerivAt (sourceResponse energy signal observable) 0 t := by
  have hden := ne_of_gt (spin_mean_variance_pos energy signal signal t hsignal hneg hpos)
  have hd := (hasDerivAt_tiltCovariance energy signal observable t hsignal).div
    (((hasDerivAt_spin_mean energy signal t hsignal).pow 2).const_sub 1) hden
  change HasDerivAt (sourceResponse energy signal observable) _ t at hd
  apply hd.congr_deriv
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hden]
  ring

theorem sourceResponse_eq (energy signal observable : S → ℝ) (t u : ℝ)
    (hsignal : ∀ s, signal s = -1 ∨ signal s = 1)
    (hneg : ∃ s, signal s = -1) (hpos : ∃ s, signal s = 1) :
    sourceResponse energy signal observable t = sourceResponse energy signal observable u := by
  exact is_const_of_deriv_eq_zero
    (fun z => (hasDerivAt_sourceResponse energy signal observable z hsignal hneg hpos).differentiableAt)
    (fun z => (hasDerivAt_sourceResponse energy signal observable z hsignal hneg hpos).deriv) t u

section Fields

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Nonempty S] in

theorem fieldMean_update_eq_mean (energy : S → ℝ) (spin : S → V → ℝ)
    (observable : S → ℝ) (x : V → ℝ) (r : V) (t : ℝ) :
    fieldMean energy spin observable (Function.update x r t) =
      mean (fieldEnergy energy spin (Function.update x r 0))
        (fun s => spin s r) observable t := by
  have hx : Function.update x r t =
      (fun v => Function.update x r 0 v + t * (if v = r then 1 else 0)) := by
    funext v
    by_cases hv : v = r <;> simp [hv]
  rw [hx, fieldMean_along_line]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem normalizedFieldCovariance_update_source (energy : S → ℝ) (spin : S → V → ℝ)
    (x : V → ℝ) (r v : V) (t u : ℝ)
    (hsignal : ∀ s, spin s r = -1 ∨ spin s r = 1)
    (hneg : ∃ s, spin s r = -1) (hpos : ∃ s, spin s r = 1) :
    normalizedFieldCovariance energy spin (fun s => spin s r) (Function.update x r t) v =
      normalizedFieldCovariance energy spin (fun s => spin s r) (Function.update x r u) v := by
  have h := sourceResponse_eq (fieldEnergy energy spin (Function.update x r 0))
    (fun s => spin s r) (fun s => spin s v) t u hsignal hneg hpos
  unfold normalizedFieldCovariance fieldCovariance
  simp only [fieldMean_update_eq_mean]
  simpa only [sourceResponse, tiltCovariance, mul_comm] using h

end Fields
end Problem367.FinitePosterior

end

end OAI
