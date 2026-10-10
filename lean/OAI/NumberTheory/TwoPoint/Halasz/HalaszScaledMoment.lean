import OAI.NumberTheory.TwoPoint.Halasz.HalaszBalancedMoment
import OAI.NumberTheory.TwoPoint.Halasz.HalaszEnergyImage
import OAI.NumberTheory.TwoPoint.Halasz.HalaszLongShortEnergy

namespace OAI

/-! Multiplying every frequency by a nonzero integer leaves each
complete-system moment unchanged. The doubled system occurs in the
collision estimate. -/
namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def halaszScaledPolynomial (k N : ℕ) (m : ℤ)
    (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  halaszFinitePhase (univ : Finset (Fin N))
    (fun x j => m*((x.val+1)^(j.val+1):ℕ)) α

lemma halasz_scaled_polynomial_continuous (k N : ℕ) (m : ℤ) :
    Continuous (halaszScaledPolynomial k N m) := halasz_finite_phase_continuous _ _

theorem halasz_scaled_moment (s k N : ℕ) (m : ℤ) (hm : m≠0) :
    (∫ α, ‖halaszScaledPolynomial k N m α‖^(2*s) ∂halaszVinogradovHaar k) =
      (halaszVinogradovCount s k N:ℝ) := by
  let f (x : Fin N) : Fin k → ℤ := fun j => m*((x.val+1)^(j.val+1):ℕ)
  let A := Fintype.piFinset (fun _ : Fin s => (univ : Finset (Fin N)))
  have h := halasz_finite_phase_energy A (fun x => ∑ i, f (x i))
  have hp (α : Fin k → AddCircle (1:ℝ)) :
      halaszFinitePhase A (fun x => ∑ i, f (x i)) α =
        (halaszScaledPolynomial k N m α)^s :=
    halasz_finite_phase_power univ f s α
  simp_rw [hp,norm_pow,← pow_mul,Nat.mul_comm s 2] at h
  have he : halaszFiberEnergy A (fun x => ∑ i, f (x i)) =
      halaszVinogradovCount s k N := by
    change halaszFiberEnergy (univ : Finset (Fin s → Fin N)) _ = _
    rw [← halasz_nat_power_energy s k N]
    apply halasz_fiber_energy_congr
    intro x _ y _
    constructor
    · intro hxy
      funext j
      have hj := congrFun hxy j
      simp only [Finset.sum_apply,f,← mul_sum,← Nat.cast_sum] at hj
      have hc := mul_left_cancel₀ hm hj
      exact_mod_cast hc
    · intro hxy
      funext j
      simp only [Finset.sum_apply,f,← mul_sum,← Nat.cast_sum]
      exact congrArg (fun t : ℕ => m*(t:ℤ)) (congrFun hxy j)
  rwa [he] at h

theorem halasz_scaled_mixed_moment {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (k N : ℕ) (m : ℤ) (hm : m≠0) :
    (∫ α, ‖halaszVinogradovPolynomial k N α‖^(2*a) *
      ‖halaszScaledPolynomial k N m α‖^(2*b) ∂halaszVinogradovHaar k) ≤
        (halaszVinogradovCount (a+b) k N : ℝ) := by
  have hF : Continuous (halaszVinogradovPolynomial k N) :=
    halasz_finite_phase_continuous _ _
  have h := halasz_equal_moment_bound (a := 2*a) (b := 2*b)
    (Nat.mul_pos (by decide : 0<2) ha) (Nat.mul_pos (by decide : 0<2) hb) (halaszVinogradovPolynomial k N)
    (halaszScaledPolynomial k N m) hF (halasz_scaled_polynomial_continuous k N m)
    (by rw [← Nat.mul_add,halasz_vinogradov_real_moment,halasz_scaled_moment _ _ _ _ hm])
  rwa [← Nat.mul_add,halasz_vinogradov_real_moment] at h

end TwoPointCorrelations

end OAI
