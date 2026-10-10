import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleZeroDegree
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.RectangleLogPrimitive

namespace OAI

/-! # Polynomial factorization and its boundary logarithmic derivative -/

open Set Function MeromorphicOn
namespace DefocusingNLS

noncomputable def countingDivisorFactor (V : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∏ a ∈ countingDivisorPoints V f, (z - a) ^ (divisor f (closedCountingRectangle V) a).toNat

theorem countingDivisorFactor_analytic (V : ℝ) (f : ℂ → ℂ) :
    AnalyticOnNhd ℂ (countingDivisorFactor V f) univ := by
  intro z _
  unfold countingDivisorFactor
  fun_prop

theorem countingDivisorFactor_eq_finprod (V : ℝ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V)) :
    countingDivisorFactor V f = ∏ᶠ a, (· - a) ^ divisor f (closedCountingRectangle V) a := by
  classical
  have hs : (fun a : ℂ => (· - a) ^ divisor f (closedCountingRectangle V) a).mulSupport ⊆
      (countingDivisorPoints V f : Set ℂ) := by
    rw [FactorizedRational.mulSupport]
    intro a ha
    exact (mem_countingDivisorPoints V f a).mpr ha
  rw [finprod_eq_prod_of_mulSupport_subset _ hs]
  funext z
  simp only [countingDivisorFactor, Finset.prod_apply, Pi.pow_apply]
  apply Finset.prod_congr rfl
  intro a ha
  symm
  simpa only [zpow_natCast] using congrArg (fun n : ℤ => (z - a) ^ n)
    (Int.toNat_of_nonneg (hf.divisor_nonneg a)).symm

theorem rectangle_finite_factorization (V : ℝ) (hV : 0 < V) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V))
    (hn : ∀ z ∈ countingRectangleBoundary V, f z ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedCountingRectangle V) ∧
      (∀ z ∈ closedCountingRectangle V, g z ≠ 0) ∧
      EqOn f (fun z => countingDivisorFactor V f z * g z) (closedCountingRectangle V) := by
  obtain ⟨g, hg, hgn, he⟩ := rectangle_extract_zeros V hV f hf hn
  have hp := countingDivisorFactor_analytic V f
  refine ⟨g, hg, hgn, analytic_eqOn_of_rectangle_codiscrete V hV f _ hf
    ((hp.mono (subset_univ _)).mul hg) ?_⟩
  simpa only [← countingDivisorFactor_eq_finprod V f hf, Pi.smul_apply, smul_eq_mul] using! he

theorem countingDivisorFactor_ne_zero (V : ℝ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V))
    (hn : ∀ z ∈ countingRectangleBoundary V, f z ≠ 0)
    (z : ℂ) (hz : z ∈ countingRectangleBoundary V) : countingDivisorFactor V f z ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro a ha
  exact pow_ne_zero _ (sub_ne_zero.mpr (countingBoundary_ne_interior hz
    (countingDivisorPoints_subset V f hf hn a ha)))

theorem countingDivisorFactor_logDeriv (V : ℝ) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedCountingRectangle V))
    (hn : ∀ z ∈ countingRectangleBoundary V, f z ≠ 0)
    (z : ℂ) (hz : z ∈ countingRectangleBoundary V) :
    logDeriv (countingDivisorFactor V f) z =
      ∑ a ∈ countingDivisorPoints V f,
        ((divisor f (closedCountingRectangle V) a).toNat : ℂ) * (z - a)⁻¹ := by
  classical
  unfold countingDivisorFactor
  rw [logDeriv_fun_prod]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [logDeriv_fun_pow (by fun_prop)]
    simp [logDeriv_apply]
  · intro a ha
    exact pow_ne_zero _ (sub_ne_zero.mpr (countingBoundary_ne_interior hz
      (countingDivisorPoints_subset V f hf hn a ha)))
  · intro a ha
    fun_prop

end DefocusingNLS

end OAI
