import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraAvoidance
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTExtraPrimeExtraction
import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalCount

namespace OAI

/-! The actual additional-band sieve controls the dyadic coefficient
error before any frequency partition or sampling. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_single_band_not_typical (P : Finset ℕ) (n : ℕ) :
    ¬mrtTypical ({()} : Finset Unit) (fun _ => P) n ↔ mrtPrimeAvoids P n := by
  simp [mrtTypical, mrtPrimeAvoids]

lemma mrt_supported_eq_single_band (P : Finset ℕ) (F : ℕ → ℂ) :
    mrtSupportedCoefficient P F =
      mrtTypicalCoefficient ({()} : Finset Unit) (fun _ => P) F := by
  funext n
  have hz : finitePrimeDivisorCount P n=0 ↔ mrtPrimeAvoids P n := by
    rw [finitePrimeDivisorCount_eq_card, card_eq_zero]
    simp only [eq_empty_iff_forall_notMem, mem_filter, not_and, mrtPrimeAvoids]
  have ht := mrt_single_band_not_typical P n
  by_cases h : mrtTypical ({()} : Finset Unit) (fun _ => P) n
  · have ha : ¬mrtPrimeAvoids P n := fun ha => (ht.mpr ha) h
    simp [mrtSupportedCoefficient, mrtTypicalCoefficient, hz, ha, h]
  · have ha : mrtPrimeAvoids P n := ht.mp h
    simp [mrtSupportedCoefficient, mrtTypicalCoefficient, hz, ha, h]

lemma mrt_avoiding_dyadic_density (P : Finset ℕ) {N : ℕ} [NeZero N]
    (δ : ℝ) (hδ : (uniformFiniteLaw (Fin N)).probability
      (fun n => mrtPrimeAvoids P (N+1+n.val)) ≤ δ) :
    (((Ioc N (2*N)).filter (fun n => mrtPrimeAvoids P n)).card:ℝ)/N ≤ δ := by
  have hh := halasz_typical_dyadic_density_bound ({()} : Finset Unit)
    (fun _ => P) δ (by simpa only [mrt_single_band_not_typical] using hδ)
  simpa only [mrt_single_band_not_typical] using hh

/-- One additional missing-band error costs only its actual density,
with a constant independent of the number of original typical bands. -/
theorem mrt_extra_missing_energy : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in Filter.atTop, ∀ (F : ℕ → ℂ), OneBounded F →
    ∀ (N : ℕ), Real.exp L ≤ N → ∀ T : ℝ, 0 < T →
      (∫ t in -T..T, ‖mrtDyadicPolynomial F N t -
        mrtDyadicPolynomial (mrtSupportedCoefficient
          (mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)) F) N t‖^2) ≤
        C*(T/N+1)*(Real.log L/L^(1/80:ℝ)) := by
  obtain ⟨C,hC,hprob⟩ := mrt_extra_prime_avoidance
  refine ⟨16*Real.exp 1*C,by positivity,?_⟩
  filter_upwards [hprob,Filter.eventually_ge_atTop (1:ℝ)] with L hprob hL
  intro F hF N hN T hT
  have hN0 : (0:ℝ) < N := (Real.exp_pos L).trans_le hN
  have hNn : 0 < N := by exact_mod_cast hN0
  let : NeZero N := ⟨hNn.ne'⟩
  let P := mrtPrimeBand (mrtExtraPrimeLower L) (mrtExtraPrimeUpper L)
  let d : ℝ := (((Ioc N (2*N)).filter (fun n => mrtPrimeAvoids P n)).card:ℝ)/N
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd : d ≤ C*(Real.log L/L^(1/80:ℝ)) := by
    exact mrt_avoiding_dyadic_density P _ (by
      simpa only [mul_div_assoc] using hprob (N+1) N hN)
  have hh := halasz_exceptional_dyadic_energy ({()} : Finset Unit)
    (fun _ => P) F hF hNn hT
  rw [← mrt_supported_eq_single_band] at hh
  simp only [mrt_single_band_not_typical] at hh
  change (∫ t in -T..T, ‖mrtDyadicPolynomial F N t -
    mrtDyadicPolynomial (mrtSupportedCoefficient P F) N t‖^2) ≤ _
  have hr : 0 ≤ T/(N:ℝ) := div_nonneg hT.le hN0.le
  calc
    _ ≤ 8*Real.exp 1*(T/N+2)*d := by
      simpa only [d,mul_div_assoc] using hh
    _ ≤ 16*Real.exp 1*(T/N+1)*d := by
      nlinarith [mul_nonneg (mul_nonneg (Real.exp_pos 1).le hd0) hr]
    _ ≤ 16*Real.exp 1*(T/N+1)*(C*(Real.log L/L^(1/80:ℝ))) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by ring

end TwoPointCorrelations

end OAI
