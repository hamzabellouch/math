import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Tactic
import OAI.NumberTheory.Ostmann.ZeroDensity.Target

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace Ostmann.ZeroDensity

def principalCumulative (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n

theorem principal_weight_nonzero_interval {φ : ℝ → ℝ}
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) {X t : ℝ} (hX : 0 < X)
    (ht : φ (t/X) ≠ 0) : t ∈ Ioo (X/2) X := by
  have h := hs (subset_tsupport φ (Function.mem_support.mpr ht))
  constructor
  · have h' := (lt_div_iff₀ hX).mp h.1
    linarith
  · have h' := (div_lt_iff₀ hX).mp h.2
    simpa using h'

theorem principal_weight_endpoints {φ : ℝ → ℝ}
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) {X : ℝ} (hX : 0 < X) :
    φ ((X/2)/X) = 0 ∧ φ (X/X) = 0 := by
  constructor
  · by_contra h
    have h' := (principal_weight_nonzero_interval hs hX h).1
    exact lt_irrefl _ h'
  · by_contra h
    have h' := (principal_weight_nonzero_interval hs hX h).2
    exact lt_irrefl _ h'

theorem principal_tsum_eq_finite (c : ℕ → ℝ) {φ : ℝ → ℝ}
    (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1) {X : ℝ} (hX : 0 < X) :
    (∑' n : ℕ, c n * φ ((n : ℝ)/X)) =
      ∑ n ∈ Finset.Ioc ⌊X/2⌋₊ ⌊X⌋₊, c n * φ ((n : ℝ)/X) := by
  apply tsum_eq_sum
  intro n hn
  have hzero : φ ((n : ℝ)/X) = 0 := by
    by_contra h
    have hi := principal_weight_nonzero_interval hs hX h
    apply hn
    exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt (by positivity : 0 ≤ X/2)).mpr hi.1,
      Nat.le_floor hi.2.le⟩
  simp only [hzero, mul_zero]

theorem principal_weight_hasDerivAt {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (X t : ℝ) : HasDerivAt (fun u : ℝ => φ (u/X)) (deriv φ (t/X) / X) t := by
  have hd : HasDerivAt φ (deriv φ (t/X)) (t/X) :=
    (hφ.differentiable (by simp) (t/X)).hasDerivAt
  simpa only [one_div, div_eq_mul_inv, Function.comp_def, id_eq, one_mul] using
    hd.comp t ((hasDerivAt_id t).div_const X)

theorem principal_weight_deriv {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (X : ℝ) :
    deriv (fun u : ℝ => φ (u/X)) = fun u => deriv φ (u/X) / X := by
  funext t
  exact (principal_weight_hasDerivAt hφ X t).deriv

theorem principal_weight_deriv_continuous {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (X : ℝ) :
    Continuous (fun u : ℝ => deriv φ (u/X) / X) :=
  ((hφ.continuous_deriv (by simp)).comp (continuous_id.div_const X)).div_const X

theorem principal_smoothing_abel (c : ℕ → ℝ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ Ioo (1/2 : ℝ) 1)
    {X : ℝ} (hX : 0 < X) :
    (∑' n : ℕ, c n * φ ((n : ℝ)/X)) =
      -(∫ t in X/2..X, (deriv φ (t/X) / X) * principalCumulative c t) := by
  have hdiff : ∀ t ∈ Icc (X/2) X, DifferentiableAt ℝ (fun u : ℝ => φ (u/X)) t :=
    fun t _ => (principal_weight_hasDerivAt hφ X t).differentiableAt
  have hint : IntegrableOn (deriv (fun u : ℝ => φ (u/X))) (Icc (X/2) X) := by
    rw [principal_weight_deriv hφ X]
    exact (principal_weight_deriv_continuous hφ X).continuousOn.integrableOn_Icc
  have h := sum_mul_eq_sub_sub_integral_mul c (by positivity : 0 ≤ X/2)
    (by linarith : X/2 ≤ X) hdiff hint
  have he := principal_weight_endpoints hs hX
  simp only [he.1, he.2, zero_mul, sub_self, zero_sub,
    principal_weight_deriv hφ X] at h
  rw [principal_tsum_eq_finite c hs hX, intervalIntegral.integral_of_le (by linarith : X/2 ≤ X)]
  simpa only [principalCumulative, mul_comm] using h

end Ostmann.ZeroDensity

end

end OAI
