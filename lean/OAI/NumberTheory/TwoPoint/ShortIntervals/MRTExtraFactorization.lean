import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraMissing
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtractionErrors

namespace OAI

/-! Complete additional-prime factorization of the actual typical
polynomial. The missing-band, prime-square and bin-boundary errors are
summed once, independently of the frequency classes. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtExtraCoarsePolynomial {ι : Type*} (L : ℝ)
    (J : Finset ι) (P : ι → Finset ℕ) (F : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  let A := mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let H := mrtExtraPrimeResolution L
  ∑ k ∈ mrtLogBins H (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L),
    mrtLogPrimePolynomial A F H k t *
      mrtCofactorPolynomial A (mrtTypicalCoefficient J P F) N (mrtPrimeLogLower H k) t

lemma mrt_extra_coarse_continuous {ι : Type*} (L : ℝ) (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (N : ℕ) :
    Continuous (mrtExtraCoarsePolynomial L J P F N) := by
  apply continuous_finsetSum
  intro k _
  exact (mrt_log_prime_polynomial_continuous _ _ _ _).mul
    (mrtCofactorPolynomial_continuous _ _ _ _)

theorem mrt_extra_factorization_energy : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in Filter.atTop, ∀ {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ),
      (∀ j ∈ J, ∀ p ∈ P j, p.Prime) →
      (∀ j ∈ J, ∀ p ∈ P j, (p:ℝ) ≤ Real.exp (Real.sqrt L)) →
    ∀ F : ℕ → ℂ, Multiplicative F → OneBounded F →
    ∀ N : ℕ, Real.exp L ≤ N → ∀ T : ℝ, 0 < T →
      (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtTypicalCoefficient J P F) N t -
        mrtExtraCoarsePolynomial L J P F N t‖^2) ≤
        C*(T/N+1)*(Real.log L/L^(1/80:ℝ)) := by
  obtain ⟨C,hC,hmissing⟩ := mrt_extra_missing_energy
  refine ⟨2*C+16896*Real.exp 1,by positivity,?_⟩
  filter_upwards [hmissing,mrt_extra_band_geometry,mrt_extra_band_disjoint,
    Filter.eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))]
    with L hmissing hg hdis hL hlog
  intro ι J P hp hmax F hF hFb N hN T hT
  let A := mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let H := mrtExtraPrimeResolution L
  let B := mrtTypicalCoefficient J P F
  let K := mrtLogBins H (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  have hB : OneBounded B := mrtTypicalCoefficient_oneBounded J P F hFb
  have hN0 : (0:ℝ) < N := (Real.exp_pos L).trans_le hN
  have hNn : 0 < N := by exact_mod_cast hN0
  have hL0 : 0 < L := by linarith
  have hH : 2 ≤ H := hg.1
  have hH0 : 0 < H := by linarith
  have hA : ∀ p ∈ A, p.Prime := fun _ hp => mrtPrimeBand_prime hp
  have hAout : Disjoint A (J.biUnion P) := by
    apply Disjoint.symm
    apply hdis
    intro p hp'
    obtain ⟨j,hj,hpj⟩ := mem_biUnion.mp hp'
    exact hmax j hj p hpj
  have hrange : ∀ p ∈ A, mrtExtraPrimeLower L ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtExtraPrimeUpper L := by
    intro p hp'
    have hh := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp'
    exact ⟨hh.1.le,hh.2⟩
  have hd := mrt_log_bin_prime_data A hH (Real.exp_pos _) hA hrange
  have hw := mrt_prime_log_width hH
  have hm := mrt_extra_prime_mean_square J P hp A hA hAout K (mrtPrimeLogBin H)
    hd.1 (mrtPrimeLogLower H) hNn hw.1 hw.2.1 hd.2 F hF hFb hT
  change (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtSupportedCoefficient A B) N t -
    mrtExtraCoarsePolynomial L J P F N t‖^2) ≤ _ at hm
  have hHP : H ≤ mrtExtraPrimeLower L := by
    calc
      H ≤ Real.sqrt L := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
      _ ≤ Real.exp (Real.sqrt L) := by linarith [Real.add_one_le_exp (Real.sqrt L)]
      _ ≤ mrtExtraPrimeLower L := hg.2.1.le
  have herr := mrt_prime_extraction_error A hH hHP (fun p hp' => (hrange p hp').1)
  have hs : (∑ p ∈ A, 1/(p:ℝ)^2)+(∑ p ∈ A, 1/(p:ℝ)^2)^2+
      (Real.exp (1/H)-1) ≤ 6/H := by linarith [hw.2.2]
  have hnorm : 1/H ≤ Real.log L/L^(1/80:ℝ) := by
    change 1/H ≤ Real.log L/H
    exact div_le_div_of_nonneg_right hlog hH0.le
  have hfactor : 0 ≤ 1408*Real.exp 1*(T/(N:ℝ)+1) := by positivity
  have hm' : (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtSupportedCoefficient A B) N t -
      mrtExtraCoarsePolynomial L J P F N t‖^2) ≤
        (8448*Real.exp 1)*(T/N+1)*(Real.log L/L^(1/80:ℝ)) := by
    apply hm.trans
    calc
      _ ≤ 1408*Real.exp 1*(T/(N:ℝ)+1)*(6/H) :=
        mul_le_mul_of_nonneg_left hs hfactor
      _ = (8448*Real.exp 1)*(T/N+1)*(1/H) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hm'':= hmissing B hB N hN T hT
  have hD : Continuous (mrtDyadicPolynomial B N) := mrtExponentialPolynomial_continuous _ _ _
  have hS : Continuous (mrtDyadicPolynomial (mrtSupportedCoefficient A B) N) :=
    mrtExponentialPolynomial_continuous _ _ _
  have hG := mrt_extra_coarse_continuous L J P F N
  have hh := mrt_restricted_energy_split
    (fun t => mrtDyadicPolynomial B N t-mrtExtraCoarsePolynomial L J P F N t)
    (fun t => mrtDyadicPolynomial (mrtSupportedCoefficient A B) N t-
      mrtExtraCoarsePolynomial L J P F N t)
    (hD.sub hG) (hS.sub hG) hT.le (Set.Subset.refl (Set.Ioc (-T) T))
  have he (t : ℝ) :
      (mrtDyadicPolynomial B N t-mrtExtraCoarsePolynomial L J P F N t)-
      (mrtDyadicPolynomial (mrtSupportedCoefficient A B) N t-
        mrtExtraCoarsePolynomial L J P F N t) =
      mrtDyadicPolynomial B N t-mrtDyadicPolynomial (mrtSupportedCoefficient A B) N t := by ring
  simp only [he,← intervalIntegral.integral_of_le (show -T ≤ T by linarith)] at hh
  apply hh.trans
  have hsum := add_le_add
    (mul_le_mul_of_nonneg_left hm'' (by norm_num : (0:ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hm' (by norm_num : (0:ℝ) ≤ 2))
  convert hsum using 1
  ring

end TwoPointCorrelations

end OAI
