import OAI.NumberTheory.JointDickman.Counting.CanonicalAffineEnergy
import OAI.NumberTheory.JointDickman.Counting.TwistedExceptionalEnergy
import OAI.NumberTheory.JointDickman.Analysis.MellinFrequencyTail

namespace OAI

/-! # Uniform spectral bounds for the actual nonprincipal interpolants -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem twisted_bin_spectral
    {ι : Type*} [Fintype ι] {J : ℕ} (hJ : 0 < J) (j : ι → ℕ) (hj : ∀ i, 1 ≤ j i)
    : ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop,
      ∀ (E : Finset ℕ), (∀ p ∈ E, p.Prime) →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ A : ℝ, 0 < A → ∀ᶠ N : ℕ in atTop,
      ∀ x : ℝ, (N:ℝ)/A ≤ x → ∀ (m : ℕ) (a : ι → Fin m) (w : ℕ → ℝ),
      (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) → ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N))
        (twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
          (finitePrimeWeight E w) a χ) t‖^2) ≤
        4/H+canonicalAffineBase C H+(canonicalAffineSlope C H+32*Real.exp 1)*T/N := by
  obtain ⟨C,hC,hcanonical⟩ := canonical_affine_energy
  refine ⟨C,hC,?_⟩
  filter_upwards [hcanonical,canonical_affine_nonneg hC.le,
    eventually_mellin_application_scales,eventually_gt_atTop (0:ℝ)] with H hcan hpos hscale hH
  obtain ⟨hP,hPQ,hlogP,hQ,hbudget,hR⟩ := hscale
  intro E hE q _ χ hχ A hA
  have hex := twisted_exceptional_energy (mellinFirstPrime H) (mellinLastPrime H)
    hP hPQ (by linarith) hQ hR hJ j hj E hE χ hχ hA (by positivity : 0<(1:ℝ)/H)
  filter_upwards [hcan hQ,hex,eventually_gt_atTop (0:ℕ)] with N hcan hex hN
  dsimp only at hcan hex
  intro x hx m a w hw
  let F := twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
    (finitePrimeWeight E w) a χ
  let B := canonicalMellinBands (mellinFirstPrime H) (mellinLastPrime H) (1/12)
  let L := mellinBandCount (mellinLastPrime H) (Real.sqrt (Real.log (N:ℝ))) hQ
  have hmult := twistedWeightedBinInterpolant_multiplicative (fun i => primeBin x J (j i)) (finitePrimeWeight E w)
    (finitePrimeWeight_multiplicative hE w) a χ
  have hnorm : ∀ n, ‖F n‖ ≤ 1 := by
    apply twistedWeightedBinInterpolant_norm_le
    intro n
    rw [abs_of_nonneg (finitePrimeWeight_bounds hw n).1]
    exact (finitePrimeWeight_bounds hw n).2
  have hall := angularMellin_extend_affine F (by norm_num : (0:ℝ)≤1) hnorm
    (show 0 ≤ 4/H+canonicalAffineBase C H from add_nonneg (by positivity) hpos.1)
    hpos.2 hN ?_
  · simpa only [one_pow,mul_one] using hall
  intro T hT hTN
  have hT0 : 0<T := by linarith
  let S := Set.Ioc (-T) T ∩ mrtNoSmallBand B.bins (B.polynomial F) B.threshold L
  have hSm : MeasurableSet S := measurableSet_Ioc.inter
    (mrt_no_small_band_measurable _ _ _ (B.polynomial_continuous F) L)
  have hSN : S ⊆ Set.Ioc (-(N:ℝ)) N := by
    intro t ht
    exact ⟨by linarith [ht.1.1],ht.1.2.trans hTN⟩
  have he := hex x hx m a w hw S hSm hSN Set.inter_subset_right
  have hc := hcan F (fun _ _ _ _ hcop => hmult.2 hcop) hnorm
    (Set.Ioc (-T) T) T measurableSet_Ioc hT0 (Set.Subset.refl _)
  rw [←intervalIntegral.integral_of_le (by linarith : -T≤T)] at hc
  change (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤ 1/H at he
  change (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤ _
  dsimp only [S,B,L] at he
  linear_combination hc + 4*he

end JointDickman

end OAI
