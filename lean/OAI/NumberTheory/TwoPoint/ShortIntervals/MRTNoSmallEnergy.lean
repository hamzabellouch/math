import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallCoarse

namespace OAI

/-! No-small-class energy, including the complete extra-band extraction
error, under the sparse-prime estimate and the cofactor pointwise bound. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

theorem mrt_no_small_energy_sharp (hprime : HalaszPrimeSparseInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), Multiplicative F → OneBounded F →
    ∀ J j : ℕ, j < J →
    (∀ i ∈ Icc 1 J, ∀ p ∈ V i, p.Prime) →
    (∀ i ∈ Icc 1 J, ∀ p ∈ V i, (p:ℝ) ≤ Real.exp (Real.sqrt L)) →
    ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) →
    200*Real.log L+1 ≤ Real.log (mrtBandLower P Q (j+1)) →
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
    ∀ N : ℕ, Real.exp L ≤ N → ∀ E : Set ℝ,
    MeasurableSet E → E ⊆ Set.Ioc (-Real.exp L) (Real.exp L) →
    (∀ t ∈ E, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
      (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) J) →
    (∀ k ∈ mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
        (mrtExtraPrimeUpper L), ∀ t ∈ E,
      L^(-100:ℝ) ≤ ‖mrtLogPrimePolynomial
        (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F
          (mrtExtraPrimeResolution L) k t‖ →
      ‖mrtCofactorPolynomial (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L))
        (mrtTypicalCoefficient (Icc 1 J) V F) N
        (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) t‖ ≤ 2*L^(-1/40:ℝ)) →
    (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t‖^2) ≤
      C*Real.log L/L^(1/80:ℝ) := by
  obtain ⟨C₀,hC₀,hcoarse⟩ := mrt_no_small_coarse_energy hprime
  obtain ⟨C₁,hC₁,hfactor⟩ := mrt_extra_factorization_energy
  refine ⟨2*C₀+4*C₁,by positivity,?_⟩
  filter_upwards [hcoarse,hfactor,Filter.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))]
    with L hcoarse hfactor hL hlog
  intro V F hF hFb J j hj hp hmax P Q hP hPQ hQ hres hrange hlo hhi N hN E hE hET hno hpoint
  have hmem : j+1 ∈ Icc 1 J := mem_Icc.mpr ⟨by omega,by omega⟩
  have hc := hcoarse V F hFb J j hj P Q hP hPQ hQ hres (hp (j+1) hmem)
    hrange hlo hhi N hN E hE hET hno hpoint
  have hf := hfactor (Icc 1 J) V hp hmax F hF hFb N hN (Real.exp L) (Real.exp_pos L)
  have hN0 : (0:ℝ) < N := (Real.exp_pos L).trans_le hN
  have hratio : Real.exp L/(N:ℝ)+1 ≤ 2 := by
    have hh := (div_le_one hN0).mpr hN
    linarith
  have hL0 : 0 < L := by linarith
  have hd : 0 ≤ Real.log L/L^(1/80:ℝ) := by positivity
  have hf' : (∫ t in -Real.exp L..Real.exp L,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t-
        mrtExtraCoarsePolynomial L (Icc 1 J) V F N t‖^2) ≤
      2*C₁*(Real.log L/L^(1/80:ℝ)) := by
    apply hf.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio hC₁.le) hd
    convert hh using 1
    ring
  have hpower : L^(-1/80:ℝ) ≤ Real.log L/L^(1/80:ℝ) := by
    calc
      _ ≤ L^(-1/80:ℝ) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ = 1/L^(1/80:ℝ) := by
        rw [show (-1/80:ℝ)=-(1/80:ℝ) by ring,Real.rpow_neg hL0.le]
        simp only [one_div]
      _ ≤ _ := div_le_div_of_nonneg_right hlog (by positivity)
  have hc' := hc.trans (mul_le_mul_of_nonneg_left hpower hC₀.le)
  have hs := mrt_restricted_energy_split
    (mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N)
    (mrtExtraCoarsePolynomial L (Icc 1 J) V F N)
    (mrtExponentialPolynomial_continuous _ _ _)
    (mrt_extra_coarse_continuous _ _ _ _ _) (Real.exp_pos L).le hET
  apply hs.trans
  have hh := add_le_add (mul_le_mul_of_nonneg_left hf' (by norm_num : (0:ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hc' (by norm_num : (0:ℝ) ≤ 2))
  convert hh using 1
  ring


/-- Monotonicity in the additional-band error bound. -/
lemma mrt_sharp_log_error_le {L : ℝ} (hL : 1 ≤ L) :
    Real.log L/L^(1/80:ℝ) ≤ Real.log L/L^(1/100:ℝ) := by
  apply div_le_div_of_nonneg_left (Real.log_nonneg hL)
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hL) _)
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

theorem mrt_no_small_energy (hprime : HalaszPrimeSparseInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), Multiplicative F → OneBounded F →
    ∀ J j : ℕ, j < J →
    (∀ i ∈ Icc 1 J, ∀ p ∈ V i, p.Prime) →
    (∀ i ∈ Icc 1 J, ∀ p ∈ V i, (p:ℝ) ≤ Real.exp (Real.sqrt L)) →
    ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) →
    200*Real.log L+1 ≤ Real.log (mrtBandLower P Q (j+1)) →
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
    ∀ N : ℕ, Real.exp L ≤ N → ∀ E : Set ℝ,
    MeasurableSet E → E ⊆ Set.Ioc (-Real.exp L) (Real.exp L) →
    (∀ t ∈ E, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
      (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) J) →
    (∀ k ∈ mrtLogBins (mrtExtraPrimeResolution L) (mrtExtraPrimeLower L)
        (mrtExtraPrimeUpper L), ∀ t ∈ E,
      L^(-100:ℝ) ≤ ‖mrtLogPrimePolynomial
        (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F
          (mrtExtraPrimeResolution L) k t‖ →
      ‖mrtCofactorPolynomial (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L))
        (mrtTypicalCoefficient (Icc 1 J) V F) N
        (mrtPrimeLogLower (mrtExtraPrimeResolution L) k) t‖ ≤ 2*L^(-1/40:ℝ)) →
    (∫ t in E, ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t‖^2) ≤
      C*Real.log L/L^(1/100:ℝ) := by
  obtain ⟨C,hC,henergy⟩ := mrt_no_small_energy_sharp hprime
  refine ⟨C,hC,?_⟩
  filter_upwards [henergy,Filter.eventually_ge_atTop (1:ℝ)] with L henergy hL
  intro V F hF hFb J j hj hp hmax P Q hP hPQ hQ hres hrange hlo hhi N hN E hE hET hno hpoint
  apply (henergy V F hF hFb J j hj hp hmax P Q hP hPQ hQ hres hrange hlo hhi
    N hN E hE hET hno hpoint).trans
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (mrt_sharp_log_error_le hL) hC.le

end TwoPointCorrelations

end OAI
