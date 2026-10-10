import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallEnergy
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMaximalBand
import OAI.NumberTheory.TwoPoint.Halasz.HalaszExtraCofactor

namespace OAI

/-! The no-small energy at the literal scale L=log N and outside the
neighborhood of an actual minimizing twist. The cofactor estimates follow
from off-center cancellation. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

noncomputable def mrtNoSmallOffCenter (P Q : ℝ) (J N : ℕ) (F : ℕ → ℂ) (τ : ℝ) : Set ℝ :=
  (Set.Ioc (-(N:ℝ)) N ∩ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
    (mrtLogFamilyPolynomial
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F P Q (1/100))
    (mrtLogFamilyThreshold P Q (1/100)) J) ∩
    {t | (Real.log N)^(1/16:ℝ) ≤ |t-τ|}

lemma mrt_no_small_off_center_measurable (P Q : ℝ) (J N : ℕ) (F : ℕ → ℂ) (τ : ℝ) :
    MeasurableSet (mrtNoSmallOffCenter P Q J N F τ) := by
  apply MeasurableSet.inter
  · exact measurableSet_Ioc.inter (mrt_no_small_band_measurable _ _ _
      (fun _ _ => mrt_log_prime_polynomial_continuous _ _ _ _) J)
  · exact (isClosed_le continuous_const (continuous_id.sub continuous_const).abs).measurableSet

theorem mrt_no_small_off_center_energy_sharp
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
    ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
    ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      2 ≤ mrtBaseResolution P Q (1/100) →
    ∀ J : ℕ, 1 ≤ J →
      200*Real.log (Real.log N)+1 ≤ Real.log (mrtBandLower P Q J) →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log N)) →
    ∀ τ : ℝ, |τ| ≤ 2*N →
      (∀ v : ℝ, |v| ≤ 2*N → squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        squaredDistance F (mrtArchimedeanTwist v) (2*N)) →
    (∫ t in mrtNoSmallOffCenter P Q J N F τ,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N t‖^2) ≤
      C*Real.log (Real.log N)/(Real.log N)^(1/80:ℝ) := by
  obtain ⟨C,hC,henergy⟩ := mrt_no_small_energy_sharp hprime
  refine ⟨C,hC,?_⟩
  have hlog : Filter.Tendsto (fun N:ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually henergy,hhigh.extra_cofactor,
    hlog.eventually mrt_extra_band_geometry,Filter.eventually_ge_atTop 2,
    hlog.eventually (Filter.eventually_ge_atTop (1:ℝ))]
    with N henergy hcofactor hg hN hL1
  intro F hF1 hFm hFb P Q hP hPQ hQ hres J hJ hlo hupper τ hτ hmin
  let V := fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)
  let L := Real.log (N:ℝ)
  let E := mrtNoSmallOffCenter P Q J N F τ
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hL0 : 0 < L := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hLL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hp : ∀ i ∈ Icc 1 J, ∀ p ∈ V i, p.Prime := fun _ _ _ hp => mrtPrimeBand_prime hp
  have hupperlog : Real.log (mrtBandUpper Q J) ≤ Real.sqrt L := by
    calc
      _ ≤ Real.log (Real.exp (Real.sqrt L)) :=
        Real.log_le_log (show 0 < mrtBandUpper Q J from Real.exp_pos _) hupper
      _ = _ := Real.log_exp _
  have hmax : ∀ i ∈ Icc 1 J, ∀ p ∈ V i, (p:ℝ) ≤ Real.exp (Real.sqrt L) := by
    intro i hi p hp'
    have hpU := (mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp').2
    have hu := (mrt_band_upper_log_mono hQ (mem_Icc.mp hi).1 (mem_Icc.mp hi).2).trans hupperlog
    have he := Real.exp_le_exp.mpr hu
    rw [Real.exp_log (show 0 < mrtBandUpper Q i from Real.exp_pos _)] at he
    exact hpU.trans he
  have hj : J-1 < J := by omega
  have hji : J-1+1=J := by omega
  have hET : E ⊆ Set.Ioc (-Real.exp L) (Real.exp L) := by
    rw [Real.exp_log hN0]
    exact fun _ ht => ht.1.1
  apply henergy V F hFm hFb J (J-1) hj hp hmax P Q hP hPQ hQ hres
  · intro p hp'
    rw [hji] at hp' ⊢
    have hh := mrtPrimeBand_bounds (Real.exp_pos _).le (Real.exp_pos _).le hp'
    exact ⟨hh.1.le,hh.2⟩
  · simpa only [hji] using hlo
  · simpa only [hji] using hupperlog
  · exact (Real.exp_log hN0).le
  · exact mrt_no_small_off_center_measurable P Q J N F τ
  · exact hET
  · exact fun _ ht => ht.1.2
  · intro k hk t ht _hlarge
    let H := mrtExtraPrimeResolution L
    let a := mrtPrimeLogLower H k
    have hH : 0 < H := by change 0 < mrtExtraPrimeResolution L; linarith [hg.1]
    have ha : 1 ≤ a := mrt_prime_log_lower_one hH k
    have haU : a ≤ Real.exp (L/Real.log L) :=
      mrt_prime_log_lower_le_upper hH (Real.one_le_exp (by positivity)) (mem_Icc.mp hk).2
    exact hcofactor F hF1 hFm hFb P Q J hQ hupper
      (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L))
      (fun _ hp' => mrtPrimeBand_prime hp') a ha haU t τ
      (abs_le.mpr ⟨ht.1.1.1.le,ht.1.1.2⟩) hτ hmin ht.2

theorem mrt_no_small_off_center_energy
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
    ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
    ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      2 ≤ mrtBaseResolution P Q (1/100) →
    ∀ J : ℕ, 1 ≤ J →
      200*Real.log (Real.log N)+1 ≤ Real.log (mrtBandLower P Q J) →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log N)) →
    ∀ τ : ℝ, |τ| ≤ 2*N →
      (∀ v : ℝ, |v| ≤ 2*N → squaredDistance F (mrtArchimedeanTwist τ) (2*N) ≤
        squaredDistance F (mrtArchimedeanTwist v) (2*N)) →
    (∫ t in mrtNoSmallOffCenter P Q J N F τ,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N t‖^2) ≤
      C*Real.log (Real.log N)/(Real.log N)^(1/100:ℝ) := by
  obtain ⟨C,hC,henergy⟩ := mrt_no_small_off_center_energy_sharp hprime hhigh
  refine ⟨C,hC,?_⟩
  have hlog : Filter.Tendsto (fun N:ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [henergy,hlog.eventually (Filter.eventually_ge_atTop (1:ℝ))]
    with N henergy hL
  intro F hF1 hFm hFb P Q hP hPQ hQ hres J hJ hlo hupper τ hτ hmin
  apply (henergy F hF1 hFm hFb P Q hP hPQ hQ hres J hJ hlo hupper τ hτ hmin).trans
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (mrt_sharp_log_error_le hL) hC.le

end TwoPointCorrelations

end OAI
