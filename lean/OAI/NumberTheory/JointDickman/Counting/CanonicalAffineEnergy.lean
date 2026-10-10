import OAI.NumberTheory.JointDickman.Counting.CanonicalFullEnergy
import OAI.NumberTheory.JointDickman.Analysis.SelectedMellinDensity
import OAI.NumberTheory.JointDickman.Amplification.CanonicalAffineCost

namespace OAI

/-! # An affine spectral bound at the canonical application scales -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem canonical_affine_energy : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ H : ℝ in atTop, ∀ hQ : 1 ≤ Real.log (mellinLastPrime H),
    ∀ᶠ N : ℕ in atTop,
      let B := canonicalMellinBands (mellinFirstPrime H) (mellinLastPrime H) (1/12)
      let J := mellinBandCount (mellinLastPrime H) (Real.sqrt (Real.log (N:ℝ))) hQ
      ∀ (F : ℕ → ℂ), Multiplicative F → (∀ n, ‖F n‖ ≤ 1) →
      ∀ (S : Set ℝ) (T : ℝ), MeasurableSet S → 0 < T →
      S ⊆ Set.Ioc (-T) T →
      (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
        4*(∫ t in S ∩ mrtNoSmallBand B.bins (B.polynomial F) B.threshold J,
          ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2)+
        canonicalAffineBase C H+canonicalAffineSlope C H*T/N := by
  obtain ⟨C,hC,hcount⟩ := selected_dyadic_missing
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_mellin_application_scales,eventually_ge_atTop (1:ℝ)] with H hscale hH
  intro hQ
  obtain ⟨hPbig,hPQ,hlogP,_hlogQ,hbudget,hR⟩ := hscale
  have hJ := ((mellinBandCount_tendsto (mellinLastPrime H) hQ).comp
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))).eventually
    (eventually_ge_atTop 1)
  filter_upwards [hcount,hJ,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 4),eventually_gt_atTop (0:ℕ)] with N hcount hJ hlogN hN
  dsimp only
  intro F hF hb S T hSm hT hS
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hP0 : 0 < mellinFirstPrime H := lt_of_lt_of_le (by positivity) hPbig
  have hP2 : 2 ≤ mellinFirstPrime H := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hh := canonical_full_energy (by exact hJ) hPbig hlogP hPQ
    (by norm_num : (0:ℝ)<1/12) (by norm_num) hbudget hR hN
    (selected_mellin_bands_fit _ _ hQ hn hlogN) F hF hb hT hSm hS
  have hd := hcount (mellinFirstPrime H) (mellinLastPrime H) (1/12) hP2 hPQ hQ
  have hbad := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 48*Real.exp 1*(T/N+2) by positivity)
  have hbad' : 48*Real.exp 1*(T/N+2)*
      (((Ioc N (2*N)).filter fun n =>
        ¬mrtTypical (range (mellinBandCount (mellinLastPrime H) (Real.sqrt (Real.log (N:ℝ))) hQ))
          (canonicalMellinBands (mellinFirstPrime H) (mellinLastPrime H) (1/12)).primes n).card:ℝ)/N ≤
      48*Real.exp 1*(T/N+2)*(C*Real.log (mellinFirstPrime H)/Real.log (mellinLastPrime H)) := by
    convert hbad using 1; ring
  dsimp only [canonicalAffineBase,canonicalAffineSlope,mellinResolution]
  linear_combination hh + hbad'

end JointDickman

end OAI
