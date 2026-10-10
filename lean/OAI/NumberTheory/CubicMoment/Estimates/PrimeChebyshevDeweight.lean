import OAI.NumberTheory.CubicMoment.Estimates.InverseLogWeight
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDyadicReconstruction
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDyadicMajorant
import OAI.NumberTheory.CubicMoment.Estimates.FixedAngularHecke

namespace OAI

/-! Removing the logarithmic prime weight by Abel summation above sqrt X.
The small primes are bounded by the actual Eisenstein lattice count. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma primeCutoffSum_split (ψ : Eisenstein → ℂ) {a b : ℝ} (hab : a ≤ b) :
    primeCutoffSum ψ b = primeCutoffSum ψ a +
      ∑ p ∈ (primeCutoff b).filter (fun p => a < norm p), ψ p := by
  classical
  rw [primeCutoffSum_on ψ hab, primeCutoffSum_eq_sum, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : norm p ≤ a
  · simp [hp,not_lt_of_ge hp]
  · simp [hp,lt_of_not_ge hp]

lemma inverseLogWeight_prime_cancel (ψ : Eisenstein → ℂ) {p : Eisenstein}
    (hp : 1 < norm p) :
    inverseLogWeight (norm p) * (ψ p * (Real.log (norm p) : ℂ)) = ψ p := by
  have hn : (Real.log (norm p) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos hp).ne'
  unfold inverseLogWeight
  push_cast
  field_simp

lemma primeChebyshev_deweight (ψ : Eisenstein → ℂ) {B c Q X X0 : ℝ}
    (hψ : ∀ p, primaryPrime p → ‖ψ p‖ ≤ 1) (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hc1 : c ≤ 1/2) (hQ : 1 ≤ Q) (hXp : 0 < X)
    (hL : 2 ≤ Real.log X) (hX0 : X0 ≤ Real.sqrt X)
    (hmain : ∀ t, X0 ≤ t →
      ‖primeChebyshev ψ t‖ ≤ B*primeCancellationWeight c Q t) :
    ‖primeCutoffSum ψ X‖ ≤ (2*B+18)*primeCancellationWeight (c/2) Q X := by
  have hx1 : 1 ≤ X := by
    have hh := Real.exp_le_exp.mpr (show (0:ℝ) ≤ Real.log X by linarith)
    simpa only [Real.exp_zero,Real.exp_log hXp] using hh
  have hroot : Real.sqrt X ≤ X := (Real.sqrt_le_iff).mpr ⟨hXp.le,by nlinarith⟩
  have hrootp : 0 < Real.sqrt X := Real.sqrt_pos.mpr hXp
  have hrootexp : Real.exp 1 ≤ Real.sqrt X := by
    apply (Real.le_log_iff_exp_le hrootp).mp
    rw [Real.log_sqrt hXp.le]
    linarith
  have hroot1 : 1 < Real.sqrt X :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hrootexp
  let H := B*primeCancellationWeight (c/2) Q X
  have hH : 0 ≤ H := by unfold H primeCancellationWeight; positivity
  have hprefix (t : ℝ) (ht : t ∈ Icc (Real.sqrt X) X) :
      ‖primeChebyshev ψ t‖ ≤ H := by
    apply (hmain t (hX0.trans ht.1)).trans
    apply (mul_le_mul_of_nonneg_left
      (primeDyadic_majorant_compare hc hQ hXp hL ht.1 ht.2) hB).trans
    unfold H primeCancellationWeight
    gcongr
    exact ht.2
  have hw := weighted_prime_bound
    (fun p => ψ p*(Real.log (norm p):ℂ)) inverseLogWeight hrootp.le hroot
    (fun t ht => (inverseLogWeight_hasDerivAt (hroot1.trans_le ht.1)).differentiableAt)
    (inverseLogWeight_integrableOn_deriv hroot1) hprefix
  have hsum : (∑ p ∈ (primeCutoff X).filter (fun p => Real.sqrt X < norm p),
      inverseLogWeight (norm p)*(ψ p*(Real.log (norm p):ℂ))) =
      ∑ p ∈ (primeCutoff X).filter (fun p => Real.sqrt X < norm p), ψ p := by
    classical
    apply Finset.sum_congr rfl
    intro p hp
    exact inverseLogWeight_prime_cancel ψ
      (hroot1.trans (Finset.mem_filter.mp hp).2)
  rw [hsum] at hw
  have hlarge : ‖∑ p ∈ (primeCutoff X).filter
      (fun p => Real.sqrt X < norm p), ψ p‖ ≤ 2*H :=
    hw.trans ((mul_le_mul_of_nonneg_left
      (inverseLogWeight_variation hrootexp hroot) hH).trans_eq (by ring))
  have hsmall := primeCutoffSum_norm_le ψ (by norm_num : (0:ℝ)≤1) hψ hrootp.le
  have hsqrt : Real.sqrt X ≤ primeCancellationWeight (c/2) Q X := by
    have hh := primeDyadic_sqrt_absorption hc hc1 hQ hXp hL hroot le_rfl
    have hP := (primeLogSize_bounds hQ hXp (by linarith : 1 ≤ Real.log X)).1
    unfold primeCancellationWeight
    calc
      _ ≤ X*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X) := hh
      _ = X*1*Real.exp (-(c/2)*Real.log X/primeContourDenominator Q X) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by nlinarith : (1:ℝ)≤(Real.log (X*Q))^2) hXp.le)
        (Real.exp_pos _).le
  rw [primeCutoffSum_split ψ hroot]
  apply (norm_add_le _ _).trans
  have hs : ‖primeCutoffSum ψ (Real.sqrt X)‖ ≤
      18*primeCancellationWeight (c/2) Q X := hsmall.trans (by nlinarith [hsqrt])
  calc
    _ ≤ 18*primeCancellationWeight (c/2) Q X+2*H := add_le_add hs hlarge
    _ = _ := by unfold H; ring

end CubicFirstMoment

end

end OAI
