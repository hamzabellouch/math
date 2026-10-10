import OAI.NumberTheory.TwoPoint.Bounds.CenteredBinIdentity
import OAI.NumberTheory.TwoPoint.Walks.CanonicalCenteringBins

namespace OAI

/-! The quantitative centering estimate for the same numerical bins
used by the spectral and deletion bounds. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def progressionLiouvilleMean (h l b : ℕ) [NeZero l] (X : ℝ) : ℂ :=
  positivePrefix (fun n => progressionSequence liouville l (b : ZMod l) n * liouville (n + h))
    ⌊X⌋₊ / (X : ℂ)

noncomputable def canonicalRawBin (h l b : ℕ) (E : Finset ℕ) (W L η X : ℝ) (j : ℤ) : ℂ :=
  let T := X * Real.exp ((j : ℝ) * η)
  ((⌊T⌋₊ : ℂ) / (T : ℂ)) *
    canonicalUncutPrefix h l b E W L (numericalBinEligible L η j) ⌊T⌋₊

theorem quantitative_centering_assembly (hP : ModFiveThetaInput)
    (hM : PrimeReciprocalInput) (hMRT : MRTLiouvilleShortInput)
    (h : ℕ) (hh : 0 < h) (l : ℕ) [NeZero l] (E : Finset ℕ)
    (hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop, ∀ _hL : 1 ≤ L,
      ∀ X : ℝ, Real.exp (L ^ (1000 : ℝ)) ≤ X →
      ∀ η : ℝ, 0 < η → η < Real.log 2 → ∀ b : ℕ,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let S₀ := totalPaddingBinMass (primeTupleDivisors P) Q L η
      ‖(∑ j ∈ paddingBinIndices L η, canonicalRawBin h l b E W L η X j) -
          (S₀ : ℂ) * progressionLiouvilleMean h l b X‖ ≤
        C * η⁻¹ * (2 : ℝ) ^ J * L ^ (-1 / 20 : ℝ) * paddingTiltNormalizer Q *
          (∏ i, primeHarmonicMass (P i)) + S₀ * (2 * η + 1 / X) := by
  obtain ⟨C, hC, hb⟩ := quantitative_canonical_centering_bins hP hM hMRT h hh l E hEl W hW
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with L hb
  intro hL X hX η hη hηlog b
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
  let D := primeTupleDivisors P
  let S₀ := totalPaddingBinMass D Q L η
  let bins := paddingBinIndices L η
  let T := fun j : ℤ => X * Real.exp ((j : ℝ) * η)
  let F := progressionLiouvilleMean h l b X
  let raw := fun j => canonicalRawBin h l b E W L η X j
  let full := fun j => fullNumericalBin D R L η j l (b : ZMod l) h (T j)
  let err := fun j => tupleNonrawBin P R actualPaddingCoefficient (numericalBinEligible L η j)
    l (b : ZMod l) h (T j)
  have hp : ∀ i, ∀ p ∈ P i, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ i k, k ≠ i → Disjoint (P i) (P k) := centeredPrimeBands_disjoint _ _ _ _
    (Real.rpow_nonneg (zero_le_one.trans hL) _) (zero_le_one.trans hW)
  have hq : ∀ p ∈ Q, p.Prime := fun _ hp => paddingPrimeSupply_prime hp
  have hR : ∀ q ∈ R, 0 < q := fun q hq' =>
    retainedPrimeDivisor_pos Q hq (mem_filter.mp hq').1
  have hD : ∀ d ∈ D, 0 < d := by
    intro d hd'
    obtain ⟨x, _, rfl⟩ := mem_image.mp hd'
    exact prod_pos fun i _ => (hp i _ (x i).property).pos
  have hunit : ∀ d ∈ D, ∀ q ∈ R, IsUnit ((q * d : ℕ) : ZMod l) := by
    intro d hd' q hq'
    obtain ⟨x, _, rfl⟩ := mem_image.mp hd'
    apply (ZMod.isUnit_iff_coprime _ l).mpr
    exact Nat.coprime_mul_iff_left.mpr
      ⟨paddingPrimeDivisor_coprime E L l hEl (mem_filter.mp hq').1,
        Nat.coprime_prod_left_iff.mpr (fun i _ =>
          centeredPrimeBands_coprime E _ W J l hEl i (x i).property)⟩
  have hident (j : ℤ) : raw j - full j = err j :=
    weighted_uncut_sub_full_bin P hp hd R hR L η j h l b hh (T j)
  have hsum : (∑ j ∈ bins, raw j) - (∑ j ∈ bins, full j) = ∑ j ∈ bins, err j := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun j _ => hident j)
  have he := hb X hX η hη hηlog (numericalBinEligible L η)
    (fun j d q he => numericalBinEligible_bin L η j d q he) (b : ZMod l)
  have hf := fullNumericalBins_error D Q hD hq L η X hL
    ((Real.exp_pos _).trans_le hX) hη.le l (b : ZMod l) h hunit
  change ‖(∑ j ∈ bins, raw j) - (S₀ : ℂ) * F‖ ≤ _
  have ht := norm_add_le ((∑ j ∈ bins, raw j) - (∑ j ∈ bins, full j))
    ((∑ j ∈ bins, full j) - (S₀ : ℂ) * F)
  rw [sub_add_sub_cancel, hsum] at ht
  exact ht.trans (add_le_add ((norm_sum_le _ _).trans he) hf)

end TwoPointCorrelations

end OAI
