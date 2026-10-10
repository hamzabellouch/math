import OAI.NumberTheory.JointDickman.Counting.CanonicalAffineEnergy
import OAI.NumberTheory.JointDickman.Counting.BinExceptionalEnergy

namespace OAI

/-! # Affine energy away from zero for the actual weighted bin labels -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem bin_away_spectral {J : ℕ} (hJ : 0 < J)
    : ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop,
    ∀ (E : Finset ℕ), (∀ p ∈ E, p.Prime) → ∀ A : ℝ, 0 < A →
    ∃ T₀ : ℝ, 0 < T₀ ∧
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, (N:ℝ)/A ≤ x →
      ∀ ζ : Fin (J-1) → ℂ, (∀ i, ‖ζ i‖ ≤ 1) →
      ∀ w : ℕ → ℝ, (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ S : Set ℝ, MeasurableSet S → ∀ T : ℝ, 0 < T → T ≤ N →
      S ⊆ Set.Ioc (-T) T → (∀ t ∈ S, T₀ ≤ |t|) →
      (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
        (finiteWeightedCoefficient
          (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E w) t‖^2) ≤
        4/H+canonicalAffineBase C H+canonicalAffineSlope C H*T/N := by
  obtain ⟨C,hC,hcanonical⟩ := canonical_affine_energy
  refine ⟨C,hC,?_⟩
  filter_upwards [hcanonical,eventually_mellin_application_scales,
    eventually_gt_atTop (0:ℝ)] with H hcan hscale hH
  obtain ⟨hP,hPQ,hlogP,hQ,hbudget,hR⟩ := hscale
  intro E hE A hA
  obtain ⟨T₀,hT₀,hex⟩ := bin_exceptional_energy (mellinFirstPrime H) (mellinLastPrime H)
    hP hPQ (by linarith) hQ hR hJ E hE hA (by positivity : 0<(1:ℝ)/H)
  refine ⟨T₀,hT₀,?_⟩
  filter_upwards [hcan hQ,hex] with N hcan hex
  dsimp only at hcan hex
  intro x hx ζ hζ w hw S hSm T hT hTN hS hST
  let F := finiteWeightedCoefficient
    (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ) E w
  let B := canonicalMellinBands (mellinFirstPrime H) (mellinLastPrime H) (1/12)
  let L := mellinBandCount (mellinLastPrime H) (Real.sqrt (Real.log (N:ℝ))) hQ
  let R := S ∩ mrtNoSmallBand B.bins (B.polynomial F) B.threshold L
  have hRm : MeasurableSet R := hSm.inter
    (mrt_no_small_band_measurable _ _ _ (B.polynomial_continuous F) L)
  have hRN : R ⊆ Set.Ioc (-(N:ℝ)) N := by
    intro t ht
    have hh := hS ht.1
    exact ⟨by linarith [hh.1],hh.2.trans hTN⟩
  have he := hex x hx ζ hζ w hw R hRm hRN Set.inter_subset_right
    (fun t ht => hST t ht.1)
  have hm := finiteWeightedCoefficient_multiplicative
    (binLabel (fun i : Fin (J-1) => primeBin x J (i.val+1)) ζ)
    (binLabel_isMultiplicative _ _) hE w
  have hn : ∀ n, ‖F n‖ ≤ 1 := finiteWeightedCoefficient_norm _
    (norm_binLabel_le_one_of_norm_le _ ζ hζ) hw
  have hc := hcan F (fun _ _ _ _ hcop => hm.2 hcop) hn S T hSm hT hS
  dsimp only [R,B,L] at he
  linear_combination hc + 4*he

end JointDickman

end OAI
