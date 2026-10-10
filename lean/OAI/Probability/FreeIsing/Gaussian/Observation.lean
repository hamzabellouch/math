import OAI.Probability.FreeIsing.Posterior.FinitePosterior

namespace OAI

noncomputable section

open ProbabilityTheory
open scoped BigOperators NNReal

namespace Problem367.GaussianObservation

theorem gaussianPDFReal_spin_tilt (t : ℝ≥0) (ht : t ≠ 0) (spin x : ℝ)
    (hspin : spin ^ 2 = 1) :
    gaussianPDFReal ((t : ℝ) * spin) t x =
      gaussianPDFReal 0 t x * Real.exp (spin * x - (t : ℝ) / 2) := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  simp only [gaussianPDFReal, sub_zero, mul_assoc, ← Real.exp_add]
  congr 2
  field_simp
  nlinarith [show ((t : ℝ) * spin) ^ 2 = (t : ℝ) ^ 2 by
    rw [mul_pow, hspin, mul_one]]

variable {V : Type*} [Fintype V]

def likelihood (t : ℝ≥0) (spin x : V → ℝ) : ℝ :=
  ∏ v, gaussianPDFReal ((t : ℝ) * spin v) t (x v)

def referenceDensity (t : ℝ≥0) (x : V → ℝ) : ℝ :=
  (∏ v, gaussianPDFReal 0 t (x v)) *
    Real.exp (-(Fintype.card V : ℝ) * (t : ℝ) / 2)

lemma referenceDensity_pos (t : ℝ≥0) (ht : t ≠ 0) (x : V → ℝ) :
    0 < referenceDensity t x := by
  apply mul_pos
  · exact Finset.prod_pos (fun v _ => gaussianPDFReal_pos 0 t (x v) ht)
  · exact Real.exp_pos _

theorem likelihood_eq_referenceDensity (t : ℝ≥0) (ht : t ≠ 0)
    (spin x : V → ℝ) (hspin : ∀ v, (spin v) ^ 2 = 1) :
    likelihood t spin x =
      referenceDensity t x * Real.exp (∑ v, spin v * x v) := by
  unfold likelihood referenceDensity
  simp_rw [gaussianPDFReal_spin_tilt t ht _ _ (hspin _)]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

variable {S : Type*} [Fintype S]

theorem normalized_gaussian_likelihood (t : ℝ≥0) (ht : t ≠ 0)
    (energy : S → ℝ) (spin : S → V → ℝ) (x : V → ℝ)
    (hspin : ∀ s v, (spin s v) ^ 2 = 1) (s : S) :
    (Real.exp (energy s) * likelihood t (spin s) x) /
        (∑ r, Real.exp (energy r) * likelihood t (spin r) x) =
      Real.exp (energy s + ∑ v, spin s v * x v) /
        (∑ r, Real.exp (energy r + ∑ v, spin r v * x v)) := by
  have heq (r : S) :
      Real.exp (energy r) * likelihood t (spin r) x =
      referenceDensity t x * Real.exp (energy r + ∑ v, spin r v * x v) := by
    rw [likelihood_eq_referenceDensity t ht _ _ (hspin r), Real.exp_add]
    ring
  simp_rw [heq]
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ (ne_of_gt (referenceDensity_pos t ht x))

end Problem367.GaussianObservation

end

end OAI
