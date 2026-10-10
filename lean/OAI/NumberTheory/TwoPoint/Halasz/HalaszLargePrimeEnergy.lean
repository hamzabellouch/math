import OAI.NumberTheory.TwoPoint.Halasz.HalaszPublishedPrime
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraSampleScale
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTSetSampling
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTGeneralTypical

namespace OAI

/-! The large-extra-prime branch of the actual cofactor product. The
only analytic premise here is the explicitly cited prime sparse input;
the large-value sample count and set-integral transfer are proved. -/
namespace TwoPointCorrelations

open Filter Finset MeasureTheory
open scoped Classical

theorem HalaszPrimeSparseInput.large_prime_product_energy
    (hprime : HalaszPrimeSparseInput) :
    ∃ C B₀ : ℝ, 0 < C ∧ 2 ≤ B₀ ∧ ∀ᶠ L : ℝ in atTop,
      ∀ H Y : ℝ, B₀ ≤ H → 2 ≤ Y → H^2 ≤ Y →
      L^(79/80:ℝ) ≤ Real.log Y → Real.log Y ≤ L → 1 ≤ Real.log Y →
      ∀ (P : Finset ℕ) (F : ℕ → ℂ),
      (∀ p ∈ P, p.Prime ∧ Y ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*Y) →
      (∀ p ∈ P, Real.log Y ≤ Real.log (p:ℝ) ∧ Real.log (p:ℝ) ≤ Real.log Y+1/H) →
      OneBounded F →
      ∀ (A : Finset ℕ) (B : ℕ → ℂ) (N : ℕ) (a U : ℝ), 0 ≤ U →
      ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioc (-Real.exp L) (Real.exp L) →
      (∀ t ∈ E, L^(-100:ℝ) ≤ ‖mrtExponentialPolynomial P
        (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖ →
        ‖mrtCofactorPolynomial A B N a t‖ ≤ U) →
      (∫ t in E ∩ {t | L^(-100:ℝ) ≤ ‖mrtExponentialPolynomial P
        (fun p => F p/(p:ℂ)) (fun p => -Real.log (p:ℝ)) t‖},
        ‖mrtExponentialPolynomial P (fun p => F p/(p:ℂ))
          (fun p => -Real.log (p:ℝ)) t * mrtCofactorPolynomial A B N a t‖^2) ≤
        C*U^2/(H*(Real.log Y)^2) := by
  obtain ⟨C,B₀,hC,hB₀,hprime⟩ := hprime.short_prime_energy
  refine ⟨4*C,B₀,by positivity,hB₀,?_⟩
  filter_upwards [hprime,mrt_extra_prime_large_samples,eventually_ge_atTop (1:ℝ)]
    with L hprime hcount hL
  intro H Y hH hY hHY hYL hYU hlogY P F hP hwindow hF A B N a U _hU E hE hET hpoint
  let Q := mrtExponentialPolynomial P (fun p => F p/(p:ℂ))
    (fun p => -Real.log (p:ℝ))
  let R := mrtCofactorPolynomial A B N a
  let D := E ∩ {t | L^(-100:ℝ) ≤ ‖Q t‖}
  have hQc : Continuous Q := mrtExponentialPolynomial_continuous _ _ _
  have hRc : Continuous R := mrtCofactorPolynomial_continuous _ _ _ _
  have hD : MeasurableSet D := hE.inter (isClosed_le continuous_const hQc.norm).measurableSet
  have hDT : D ⊆ Set.Ioc (-Real.exp L) (Real.exp L) :=
    fun _ ht => hET ht.1
  have hsamples (S : Finset ℝ) (hS : ∀ t ∈ S, t ∈ D)
      (hsep : ∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) :
      (∑ t ∈ S, ‖Q t*R t‖^2) ≤ U^2*(C/(H*(Real.log Y)^2)) := by
    have hheight : ∀ t ∈ S, |t| ≤ Real.exp L := by
      intro t ht
      exact abs_le.mpr ⟨(hDT (hS t ht)).1.le,(hDT (hS t ht)).2⟩
    have hcard := hcount Y (Real.exp L) (by linarith) hYL hYU
      (Real.one_lt_exp_iff.mpr (by linarith)) le_rfl P
      (fun p hp => (hP p hp).1) (fun p hp => (hP p hp).2) F hF S hheight hsep
      (fun t ht => (hS t ht).2)
    have hp := hprime H Y hH hY hHY hYL hlogY P F hP hwindow hF S hheight hsep hcard
    calc
      _ = ∑ t ∈ S, ‖Q t‖^2*‖R t‖^2 := by
        apply sum_congr rfl
        intro t _
        rw [norm_mul,mul_pow]
      _ ≤ ∑ t ∈ S, ‖Q t‖^2*U^2 := by
        apply sum_le_sum
        intro t ht
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact pow_le_pow_left₀ (norm_nonneg _) (hpoint t (hS t ht).1 (hS t ht).2) 2
      _ = U^2*∑ t ∈ S, ‖Q t‖^2 := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro t _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (sq_nonneg U)
  have hi := mrt_set_integral_of_samples (fun t => ‖Q t*R t‖^2)
    ((hQc.mul hRc).norm.pow 2) (fun _ => sq_nonneg _) hD
    (Real.exp_pos L).le hDT hsamples
  change (∫ t in D, ‖Q t*R t‖^2) ≤ _
  apply hi.trans_eq
  ring

end TwoPointCorrelations

end OAI
