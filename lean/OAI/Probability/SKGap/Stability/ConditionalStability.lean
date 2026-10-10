import Mathlib
import OAI.Probability.SKGap.Localization.ConditionalWellDefined
import OAI.Probability.SKGap.Localization.ConditionalHessianLaw
import OAI.Probability.SKGap.Gaussian.GaussianTiltMass

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

theorem conditional_field_stability {j A R t0 T : ℝ}
    (hj : 0 < j) (hj1 : j < 1) (hA : 1 ≤ A) (hsub : sqrt j*A < 1)
    (hR : 0 ≤ R) (ht0 : 0 < t0) :
    ∃ m ν σ0 : ℝ, 0 < m ∧ 0 < ν ∧ 0 < σ0 ∧
    ∃ U : Set (ScalarTimeDomain R t0 T), IsOpen U ∧ scalarEqualitySet j R t0 T ⊆ U ∧
    ∀ R1 : ℝ, 1 ≤ R1 → ∃ ε c : ℝ, ∃ N : ℕ, 0 < ε ∧ 0 < c ∧ 0 < N ∧
    ∀ (n : ℕ) [NeZero n], N ≤ n → ∀ x ∈ U, ∀ y : Fin n → ℝ,
    empiricalLaw y=(x.1 : ProbabilityMeasure ℝ) →
    (∑ i,if R1 < |y i| then y i^2 else 0) ≤ ν*(n:ℝ) →
    ∀ σ : ℝ, |σ| ≤ σ0 →
    (conditionalGoeLaw (j/(n:ℝ)) ((x.2:ℝ)+σ^2) (magnetization y)
      (empiricalObservation j x.2 σ y)).real
      {W | ((fun i k=>W (i,k)),y) ∈ badFieldSet n j A ε m} ≤ exp (-c*(n:ℝ)) := by
  obtain ⟨m,ν,σ0,hm,hν,hσ0,U,hU,hKU,hbound⟩ :=
    conditional_empirical_simultaneous (T := T) hj hj1 hA hsub hR ht0
  let V : Set (ScalarTimeDomain R t0 T) := {x | 0 < scalarQMoment (x.1:ProbabilityMeasure ℝ)}
  have hV : IsOpen V := isOpen_lt continuous_const
    (continuous_scalarQMoment.comp (continuous_subtype_val.comp continuous_fst))
  have hKV : scalarEqualitySet j R t0 T ⊆ V := by
    intro x hx
    change 0 < scalarQMoment (x.1:ProbabilityMeasure ℝ)
    rw [hx,scalarQMoment_curve hj hj1 (ht0.le.trans x.2.2.1)]
    exact (scalar_fixed_pos hj hj1 (ht0.trans_le x.2.2.1)).2
  refine ⟨m/2,ν,σ0,half_pos hm,hν,hσ0,U∩V,hU.inter hV,fun x hx=>⟨hKU hx,hKV hx⟩,?_⟩
  intro R1 hR1
  obtain ⟨ε,c,N,hε,hc,hN,hb⟩ := hbound R1 hR1
  obtain ⟨M,hM⟩ := absorb_finite_exponential_factor 103 (half_pos hc)
  refine ⟨ε,c/2,max N M,hε,half_pos hc,lt_of_lt_of_le hN (le_max_left _ _),?_⟩
  intro n _ hn x hx y hP hy σ hσ
  have hq : 0 < scalarQMoment (empiricalLaw y) := by rw [hP]; exact hx.2
  apply (conditional_bad_le_freshbad hj.le (ht0.trans_le x.2.2.1) (by linarith : m/2 < m) y hq).trans
  apply (hb n ((le_max_left N M).trans hn) x hx.1 y hP hy σ hσ).trans
  simpa only [Nat.cast_ofNat,show (n:ℝ)*(-c)= -c*(n:ℝ) from by ring,
    show (n:ℝ)*(-c+c/2)= -(c/2)*(n:ℝ) from by ring] using
    hM n ((le_max_right N M).trans hn) (-c)
end SKGap
end
end

end OAI
