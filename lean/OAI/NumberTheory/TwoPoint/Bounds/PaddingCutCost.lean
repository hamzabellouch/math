import OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingCuts
import OAI.NumberTheory.TwoPoint.Bounds.PrimePaddingFactorization

namespace OAI

/-! The two padding deletions with the positive tuple weight retained.
The literal rejection function depends only on Q residues. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def paddingRejectedMass (Q D : Finset ℕ) (bins : Finset ℤ)
    (η c L K : ℝ) (n : ℤ) : ℝ :=
  (actualPaddingVertex Q n) ^ 2 *
    ∑ j ∈ bins, if ¬integerEdgeKeep D actualPaddingCoefficient (actualPaddingBin η c j)
      (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n then
        paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
          (actualPaddingVertex Q) n else 0

lemma paddingRejectedMass_nonneg (Q D : Finset ℕ) (bins : Finset ℤ)
    (η c L K : ℝ) (n : ℤ) : 0 ≤ paddingRejectedMass Q D bins η c L K n := by
  apply mul_nonneg (sq_nonneg _)
  apply sum_nonneg
  intro j _
  have hd := actualPaddingDensity_nonneg Q D (actualPaddingBin η c j) n
  split_ifs <;> linarith

lemma paddingRejectedMass_residue_congr (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (D : Finset ℕ) (hD : D ⊆ retainedPrimeDivisors Q)
    (bins : Finset ℤ) (η c L K : ℝ) (n m : ℤ)
    (hnm : ∀ p ∈ Q, (n : ZMod p) = (m : ZMod p)) :
    paddingRejectedMass Q D bins η c L K n = paddingRejectedMass Q D bins η c L K m := by
  unfold paddingRejectedMass
  rw [actualPaddingVertex_residue_congr Q n m hnm]
  congr 1
  apply sum_congr rfl
  intro j _
  simp only [actualPaddingKeep_residue_congr Q hQ D hD (actualPaddingBin η c j) L K n m hnm,
    actualPaddingDensity_residue_congr Q hQ D hD (actualPaddingBin η c j) n m hnm]

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

lemma positive_prime_padding_factor (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (site : ℤ) (g : ℤ → ℝ)
    (hg : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → g n = g m) :
    (data.residueLaw B hB).average (fun x =>
      positivePrimeWeight S (data.residueOrigin x + site) * g (data.residueOrigin x + site)) =
      positivePrimeNormalizer S *
        (data.residueLaw B hB).average (fun x => g (data.residueOrigin x + site)) := by
  rw [data.positive_prime_padding_average hB S hSP site g hg,
    data.residue_average_padding_shift hB site g hg]

end ProhibitedPrimeFamily

theorem ModFiveThetaInput.eventually_positive_padding_cut_cost
    (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (η c K : ℝ) (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ) (bins : Finset ℤ),
      0 < η → η ≤ 1 → 0 < K →
      ∀ (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      ∀ (S : Finset ℕ), S ⊆ data.P →
      (data.residueLaw B hB).average (fun x =>
        positivePrimeWeight S (data.residueOrigin x + site) *
          paddingRejectedMass data.Q D bins η c L K (data.residueOrigin x + site)) /
            paddingTiltNormalizer data.Q ≤
              positivePrimeNormalizer S * (C / K + L ^ (-100 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := hP.eventually_actual_padding_keep_loss E
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with L hb
  intro η c K h J M B data hQ hB site bins hη hηone hK D hD S hSP
  have hg := paddingRejectedMass_residue_congr data.Q data.primeQ D hD bins η c L K
  have he := data.positive_prime_padding_factor hB S hSP site
    (paddingRejectedMass data.Q D bins η c L K) hg
  rw [he]
  calc
    _ = positivePrimeNormalizer S *
        ((data.residueLaw B hB).average (fun x =>
          paddingRejectedMass data.Q D bins η c L K (data.residueOrigin x + site)) /
            paddingTiltNormalizer data.Q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hb η c K h J M B data hQ site bins hη hηone hK hB D hD)
      (by unfold positivePrimeNormalizer; positivity)

theorem ModFiveThetaInput.eventually_tuple_padding_cut_cost
    (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (η c K : ℝ) (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ) (bins : Finset ℤ),
      0 < η → η ≤ 1 → 0 < K →
      ∀ (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      ∀ (d : ℕ), Squarefree d → d.primeFactors.card = J → d.primeFactors ⊆ data.P →
      (data.residueLaw B hB).average (fun x =>
        positivePrimeWeight d.primeFactors (data.residueOrigin x + site) *
          paddingRejectedMass data.Q D bins η c L K (data.residueOrigin x + site)) /
            paddingTiltNormalizer data.Q ≤
              ((2 : ℝ) ^ J / d) * (C / K + L ^ (-100 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := hP.eventually_positive_padding_cut_cost E
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with L hb
  intro η c K h J M B data hQ hB site bins hη hηone hK D hD d hd hdJ hdP
  simpa only [positivePrimeNormalizer_squarefree d hd, hdJ] using
    hb η c K h J M B data hQ hB site bins hη hηone hK D hD d.primeFactors hdP

end TwoPointCorrelations

end OAI
