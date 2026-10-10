import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallCard
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraBandGeometry

namespace OAI

/-! Small additional-prime values on the actual no-small class. The
integer-kernel error is paid by the final original-band sample count. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_small_cofactor_integral (A : Finset ℕ) (B : ℕ → ℂ)
    (hB : OneBounded B) (N : ℕ) {a T θ : ℝ} (ha : 1 ≤ a)
    (hx : 2 ≤ (N:ℝ)/a) (hT : 0 ≤ T) (Q : ℝ → ℂ) (hQ : Continuous Q)
    {E : Set ℝ} (hE : MeasurableSet E) (hET : E ⊆ Set.Ioc (-T) T)
    (hcost : ∀ S : Finset ℝ, (∀ t ∈ S, t ∈ E) →
      (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
      (S.card:ℝ)*halaszSparseKernelError ((N:ℝ)/a) T ≤ (N:ℝ)/a)
    (hsmall : ∀ t ∈ E, ‖Q t‖ ≤ θ) :
    (∫ t in E, ‖Q t*mrtCofactorPolynomial A B N a t‖^2) ≤ 1190408*θ^2 := by
  have hh := mrt_set_integral_of_samples
    (fun t => ‖Q t*mrtCofactorPolynomial A B N a t‖^2)
    ((hQ.mul (mrtCofactorPolynomial_continuous A B N a)).norm.pow 2)
    (fun _ => sq_nonneg _) hE hT hET (B := 297602*θ^2) (by
      intro S hS hsep
      have hfreq : ∀ t ∈ S, |t| ≤ T := by
        intro t ht
        obtain ⟨hl,hu⟩ := hET (hS t ht)
        exact abs_le.mpr ⟨by linarith,hu⟩
      have he := halasz_sparse_cofactor_bounded A B hB N ha hx hT S hfreq hsep
        (hcost S hS hsep)
      calc
        _ ≤ ∑ t ∈ S, θ^2*‖mrtCofactorPolynomial A B N a t‖^2 := by
          apply sum_le_sum
          intro t ht
          rw [norm_mul,mul_pow]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (hsmall t (hS t ht)) 2) (sq_nonneg _)
        _ = θ^2*∑ t ∈ S, ‖mrtCofactorPolynomial A B N a t‖^2 := (mul_sum _ _ _).symm
        _ ≤ θ^2*297602 := mul_le_mul_of_nonneg_left he (sq_nonneg _)
        _ = _ := by ring)
  linarith

theorem mrt_extra_small_integral :
    ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), OneBounded F →
    ∀ J j : ℕ, j < J → ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), p.Prime) →
    (∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) →
    200*Real.log L+1 ≤ Real.log (mrtBandLower P Q (j+1)) →
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
    ∀ T : ℝ, 1 < T → T ≤ Real.exp L → ∀ N : ℕ, Real.exp L ≤ N →
    ∀ B : ℕ → ℂ, OneBounded B → ∀ k ∈
      mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L),
    ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioc (-T) T →
    (∀ t ∈ E, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
      (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) J) →
    (∀ t ∈ E, ‖mrtLogPrimePolynomial
      (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F
        (mrtExtraPrimeResolution L) k t‖ ≤ L^(-100:ℝ)) →
    (∫ t in E, ‖mrtLogPrimePolynomial
      (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F
        (mrtExtraPrimeResolution L) k t *
      mrtCofactorPolynomial (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L))
        B N (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) t‖^2) ≤
      1190408*(L^(-100:ℝ))^2 := by
  filter_upwards [mrt_no_small_card_at_scale,halasz_sparse_sample_cost,
    mrt_extra_band_geometry,Filter.eventually_ge_atTop (2:ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1000:ℝ))]
    with L hcard hcost hg hL hlog
  intro V F hF J j hj P Q hP hPQ hQ hres hp hrange hlo hhi T hT hTU N hN B hB k hk
    E hE hET hno hsmall
  let A := mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let H := mrtExtraPrimeResolution L
  let a := mrtPrimeLogLower H k
  have hL0 : 0 ≤ L := by linarith
  have hH : 0 < H := by change 0 < mrtExtraPrimeResolution L; linarith [hg.1]
  have ha : 1 ≤ a := mrt_prime_log_lower_one hH k
  have ha0 : 0 < a := by linarith
  have haU : a ≤ Real.exp (L/Real.log L) := by
    exact mrt_prime_log_lower_le_upper hH (Real.one_le_exp (by positivity)) (mem_Icc.mp hk).2
  have hM := halasz_extra_cofactor_length hL0 hlog ha0 haU hN
  have hM2 : 2 ≤ (N:ℝ)/a := by
    have hh := Real.add_one_le_exp ((999/1000:ℝ)*L)
    linarith
  apply mrt_small_cofactor_integral A B hB N ha hM2 (by linarith : 0 ≤ T)
    (mrtLogPrimePolynomial A F H k) (mrt_log_prime_polynomial_continuous A F H k) hE hET
  · intro S hS hsep
    have hfreq : ∀ t ∈ S, |t| ≤ T := by
      intro t ht
      obtain ⟨hl,hu⟩ := hET (hS t ht)
      exact abs_le.mpr ⟨by linarith,hu⟩
    have hc := hcard V F hF J j hj P Q hP hPQ hQ hres hp hrange hlo hhi T hT hTU
      S hfreq hsep (fun t ht => hno t (hS t ht))
    exact hcost ((N:ℝ)/a) T S.card hM (by linarith) hTU (Nat.cast_nonneg _) hc
  · exact hsmall

end TwoPointCorrelations

end OAI
