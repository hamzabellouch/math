import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFirstClassEnergy
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLaterClassEnergy

namespace OAI

/-! The actual logarithmic prime-polynomial family in the finite
first-small partition. Index `r` corresponds to prime band `r+1`. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped Classical

noncomputable def mrtLogFamilyBins (P Q η : ℝ) (r : ℕ) : Finset ℕ :=
  mrtLogBins (mrtResolution P Q η (r+1))
    (mrtBandLower P Q (r+1)) (mrtBandUpper Q (r+1))

noncomputable def mrtLogFamilyPolynomial (V : ℕ → Finset ℕ) (F : ℕ → ℂ)
    (P Q η : ℝ) (r k : ℕ) : ℝ → ℂ :=
  mrtLogPrimePolynomial (V (r+1)) F (mrtResolution P Q η (r+1)) k

noncomputable def mrtLogFamilyThreshold (P Q η : ℝ) (r k : ℕ) : ℝ :=
  Real.exp (-mrtFrequencyExponent η r *
    Real.log (mrtPrimeLogLower (mrtResolution P Q η (r+1)) k))

noncomputable def mrtFirstLogClass (V : ℕ → Finset ℕ) (F : ℕ → ℂ)
    (P Q η : ℝ) (r : ℕ) (T : ℝ) : Set ℝ :=
  Ioc (-T) T ∩ mrtFirstSmallBand (mrtLogFamilyBins P Q η)
    (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) r

lemma mrt_first_log_class_zero (V : ℕ → Finset ℕ) (F : ℕ → ℂ)
    {P Q η : ℝ} (hP : 0 < P) (hQ : 0 < Q) (T : ℝ) :
    mrtFirstLogClass V F P Q η 0 T =
      Ioc (-T) T ∩ mrtLogSmallSet (V 1) F (mrtBaseResolution P Q η)
        (mrtLogBins (mrtBaseResolution P Q η) P Q) (mrtFrequencyExponent η 0) := by
  ext t
  simp [mrtFirstLogClass, mrtFirstSmallBand, mrtSmallFrequencyBand, mrtLogFamilyBins,
    mrtLogFamilyPolynomial, mrtLogFamilyThreshold, mrtResolution_one,
    mrtBandLower_one _ _ hP, mrtBandUpper_one _ hQ, mrtLogSmallSet]

lemma mrt_first_log_class_succ_subset (V : ℕ → Finset ℕ) (F : ℕ → ℂ)
    (P Q η : ℝ) (j : ℕ) (T : ℝ) :
    mrtFirstLogClass V F P Q η (j+1) T ⊆
      mrtLaterLogClass (V (j+1)) (V (j+2)) F P Q η j T := by
  intro t ht
  obtain ⟨b, hb, hlarge⟩ := mrt_later_band_large_witness
    (mrtLogFamilyBins P Q η) (mrtLogFamilyPolynomial V F P Q η)
    (mrtLogFamilyThreshold P Q η) (by omega : 0 < j+1) ht.2
  have he : j+1-1 = j := by omega
  rw [he] at hb hlarge
  refine ⟨ht.1, ?_, b, hb, hlarge⟩
  intro k hk
  have hh := ht.2.1 k hk
  simpa only [mrtLogFamilyPolynomial, mrtLogFamilyThreshold, Nat.add_assoc] using hh

theorem mrt_log_partition_integral (V : ℕ → Finset ℕ) (J : ℕ)
    (F : ℕ → ℂ) (P Q η : ℝ) {N : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t‖^2) =
      (∫ t in Ioc (-T) T ∩ mrtNoSmallBand (mrtLogFamilyBins P Q η)
        (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t‖^2) +
      ∑ r ∈ range J, ∫ t in mrtFirstLogClass V F P Q η r T,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t‖^2 := by
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  exact mrt_frequency_partition_integral (mrtLogFamilyBins P Q η)
    (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η)
    (fun _ _ => mrt_log_prime_polynomial_continuous _ _ _ _) J measurableSet_Ioc
    (fun t => ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J) V F) N t‖^2)
    (mrt_continuous_square_integrable (mrtExponentialPolynomial_continuous _ _ _) hT
      (Subset.refl _))

end TwoPointCorrelations

end OAI
