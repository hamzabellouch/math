import OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry
import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts

namespace OAI

namespace PiExponent.WeightedHomogeneousSubstitution
noncomputable section
open scoped BigOperators
open MvPolynomial
open WeightedSliceDegree
open PiExponentSeshadri.Projective


variable {σ ι K : Type*}

theorem supportBound_substitution [Field K] (ρ : ι → ℝ) (B : ℝ)
    (a : σ → ι →₀ ℕ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B)
    (n : ℕ) (p : MvPolynomial.homogeneousSubmodule σ K n) :
    SupportBound ρ ((n : ℝ) * B)
      (MvPolynomial.aeval (fun j => MvPolynomial.monomial (a j) (1 : K)) p.val) := by
  classical
  refine supportBound_aeval (fun _ : σ => B) ρ
    (fun j => MvPolynomial.monomial (a j) (1 : K)) ?_ ((n : ℝ) * B) p.val ?_
  · intro j b hb
    have he : b = a j := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
    simpa only [he] using ha j
  · intro b hb
    have hd : b.degree = n := by
      exact (p.property.degree_eq_sum_deg_support hb).symm
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
      ← Finset.sum_mul, ← Nat.cast_sum, ← Finsupp.degree_apply, hd, le_refl]

theorem dehomogenize_substitution [CommRing K] (a : σ → ι →₀ ℕ)
    (z : σ) (hz : a z = 0) (p : MvPolynomial σ K) :
    MvPolynomial.aeval (fun j : ChartVariables z => MvPolynomial.monomial (a j.val) (1 : K))
      (dehomogenize z p) =
    MvPolynomial.aeval (fun j => MvPolynomial.monomial (a j) (1 : K)) p := by
  classical
  have he :
      (MvPolynomial.aeval (R := K) (fun j : ChartVariables z =>
        MvPolynomial.monomial (a j.val) (1 : K))).toRingHom.comp (dehomogenize (R := K) z) =
      (MvPolynomial.aeval (R := K) (fun j => MvPolynomial.monomial (a j) (1 : K))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [dehomogenize]
    · intro j
      by_cases hj : j = z
      · subst j
        simp [dehomogenize, hz]
      · simp [dehomogenize, hj]
  exact RingHom.congr_fun he p

theorem admissible_exponent_budget {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)
    (j : AdmissibleBlowupGeometry.Index d) :
    Finsupp.weight (fun i => (d.curveDegreeWeights i : ℝ))
      (AdmissibleBlowupGeometry.exponents d j) ≤ (AdmissibleBlowupGeometry.scale d).radius := by
  have hq := (AdmissibleBlowupGeometry.scale d).budget d.curveDegreeWeights_pos j
  have hr : (∑ i, (d.curveDegreeWeights i : ℝ) *
      (AdmissibleBlowupGeometry.exponents d j i : ℝ)) ≤
      (AdmissibleBlowupGeometry.scale d).radius := by
    exact_mod_cast hq
  simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hr

theorem admissible_supportBound {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)
    (n : ℕ) (p : MvPolynomial.homogeneousSubmodule (AdmissibleBlowupGeometry.Index d) ℂ n) :
    SupportBound (fun i => (d.curveDegreeWeights i : ℝ))
      ((n : ℝ) * (AdmissibleBlowupGeometry.scale d).radius)
      (MvPolynomial.aeval (fun j =>
        MvPolynomial.monomial (AdmissibleBlowupGeometry.exponents d j) (1 : ℂ)) p.val) :=
  supportBound_substitution _ _ _ (admissible_exponent_budget d) n p

theorem admissible_dehomogenize_substitution {ν Λ D : ℝ}
    (d : AdmissibleParameters ν Λ D)
    (p : MvPolynomial (AdmissibleBlowupGeometry.Index d) ℂ) :
    MvPolynomial.aeval (fun j : ChartVariables (AdmissibleBlowupGeometry.constantIndex d) =>
      MvPolynomial.monomial (AdmissibleBlowupGeometry.exponents d j.val) (1 : ℂ))
      (dehomogenize (AdmissibleBlowupGeometry.constantIndex d) p) =
    MvPolynomial.aeval (fun j =>
      MvPolynomial.monomial (AdmissibleBlowupGeometry.exponents d j) (1 : ℂ)) p :=
  dehomogenize_substitution _ _
    ((AdmissibleBlowupGeometry.scale d).exponents_constant d.curveDegreeWeights_pos) p

end
end PiExponent.WeightedHomogeneousSubstitution

end OAI
