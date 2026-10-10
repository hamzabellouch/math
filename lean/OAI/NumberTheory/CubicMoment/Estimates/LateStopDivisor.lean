import OAI.NumberTheory.CubicMoment.Decomposition.StoppedPrimePredicate
import OAI.NumberTheory.CubicMoment.Estimates.SieveMobius

namespace OAI

/-! A late ordinary stop contains the required large smooth divisor.
The divisor is the actual product of selected prime factors at or below
the roughness boundary, not an auxiliary existence hypothesis. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def lateStopDivisor (bin : Eisenstein → ℕ) (h : ℕ) (d : Eisenstein) : Eisenstein :=
  ∏ p ∈ (primaryPrimeFactors d).filter (fun p => h ≤ bin p), p

theorem stopped_late_smooth_divisor
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (j k h : ℕ) (Z Q M : ℝ)
    {r d : Eisenstein} (_hr : primary r) (hd : primary d) (hsd : Squarefree d)
    (hQ : 0 < Q) (hstop : stoppedSideTest bin ell j k h Z Q false r d)
    (hell : ∀ p ∈ primaryPrimeFactors d, 0 < ell (bin p) ∧ ell (bin p) ≤ norm p)
    (hsmall : ∀ p ∈ primaryPrimeFactors d, h ≤ bin p → norm p ≤ M) :
    primary (lateStopDivisor bin h d) ∧ Squarefree (lateStopDivisor bin h d) ∧
      lateStopDivisor bin h d ∣ r*d ∧ Z/Q < norm (lateStopDivisor bin h d) ∧
      ∀ p ∈ primaryPrimeFactors (lateStopDivisor bin h d), norm p ≤ M := by
  let U := (primaryPrimeFactors d).filter (fun p => h ≤ bin p)
  have hU : ∀ p ∈ U, primaryPrime p := fun p hp =>
    (primaryPrimeFactor_spec hd (Finset.mem_filter.mp hp).1).1
  have hprimary : primary (∏ p ∈ U, p) :=
    primary_finset_prod U (fun p => p) (fun p hp => (hU p hp).1)
  have hdiv : (∏ p ∈ U, p) ∣ d := by
    rw [←primaryPrimeFactors_prod hd hsd]
    exact Finset.prod_dvd_prod_of_subset U (primaryPrimeFactors d) (fun p => p)
      (Finset.filter_subset _ _)
  have hsplit : primeSurrogate (primaryPrimeFactors d) bin ell =
      primeSurrogate (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell *
        primeSurrogate U bin ell := by
    unfold primeSurrogate primeBinPrefix
    rw [←Finset.prod_filter_mul_prod_filter_not (primaryPrimeFactors d) (fun p => bin p < h)]
    congr 1
    apply Finset.prod_congr
    · ext p
      simp only [U,Finset.mem_filter,not_lt]
    · intro p hp
      rfl
  have hlo : 0 < primeSurrogate U bin ell :=
    Finset.prod_pos (fun p hp => (hell p (Finset.mem_filter.mp hp).1).1)
  have hnorm : primeSurrogate U bin ell ≤ norm (∏ p ∈ U, p) := by
    rw [norm_finset_prod]
    apply Finset.prod_le_prod₀
    · intro p hp
      exact (hell p (Finset.mem_filter.mp hp).1).1.le
    · intro p hp
      exact (hell p (Finset.mem_filter.mp hp).1).2
  have hfailed : norm r*primeSurrogate (primeBinPrefix (primaryPrimeFactors d) bin h) bin ell < Q := by
    rcases hstop.2 with hf | hf
    · cases hf
    · exact hf
  have hcross : Z ≤ norm r*primeSurrogate (primaryPrimeFactors d) bin ell := hstop.1.2.2.2
  have hlarge : Z/Q < primeSurrogate U bin ell := by
    apply (div_lt_iff₀ hQ).mpr
    rw [hsplit,←mul_assoc] at hcross
    exact hcross.trans_lt (by nlinarith [mul_lt_mul_of_pos_right hfailed hlo])
  refine ⟨hprimary,primaryPrime_product_squarefree U hU,
    hdiv.trans (dvd_mul_left d r),hlarge.trans_le hnorm,?_⟩
  intro p hp
  change p ∈ primaryPrimeFactors (∏ q ∈ U, q) at hp
  rw [primaryPrimeFactors_finset_prod U hU] at hp
  exact hsmall p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2

end CubicFirstMoment

end

end OAI
