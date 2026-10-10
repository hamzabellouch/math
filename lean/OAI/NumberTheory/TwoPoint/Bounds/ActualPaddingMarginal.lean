import OAI.NumberTheory.TwoPoint.Bounds.ResidueRestriction
import OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingResidues

namespace OAI

/-! The actual padding estimates under the full tuple-and-padding residue
law.  All dependence on the tuple coordinates is removed by the proved
product-law restriction identity. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

lemma residue_average_padding_squares
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (D : Finset ℕ)
    (hD : D ⊆ retainedPrimeDivisors data.Q) (site : ℤ)
    (η c : ℝ) (bins : Finset ℤ) :
    (data.residueLaw B hB).average (fun x =>
      (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2 *
        ∑ j ∈ bins, (paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
          (actualPaddingVertex data.Q) (data.residueOrigin x + site)) ^ 2) =
    (data.paddingResidueLaw B hB).average (fun x =>
      (actualPaddingVertex data.Q (data.paddingResidueOrigin x + site)) ^ 2 *
        ∑ j ∈ bins, (paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
          (actualPaddingVertex data.Q) (data.paddingResidueOrigin x + site)) ^ 2) := by
  apply data.residue_average_padding_shift hB site (fun n =>
    (actualPaddingVertex data.Q n) ^ 2 * ∑ j ∈ bins,
      (paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
        (actualPaddingVertex data.Q) n) ^ 2)
  intro n m hnm
  rw [actualPaddingVertex_residue_congr data.Q n m hnm]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [actualPaddingDensity_residue_congr data.Q data.primeQ D hD _ n m hnm]

lemma residue_average_padding_degree_tail
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ) (L : ℝ) :
    (data.residueLaw B hB).average (fun x =>
      (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2 *
        if ¬actualPaddingDegreeCut data.Q L (data.residueOrigin x + site) then 1 else 0) =
    (data.paddingResidueLaw B hB).average (fun x =>
      (actualPaddingVertex data.Q (data.paddingResidueOrigin x + site)) ^ 2 *
        if ¬actualPaddingDegreeCut data.Q L (data.paddingResidueOrigin x + site) then 1 else 0) := by
  apply data.residue_average_padding_shift hB site (fun n =>
    (actualPaddingVertex data.Q n) ^ 2 *
      if ¬actualPaddingDegreeCut data.Q L n then 1 else 0)
  intro n m hnm
  rw [actualPaddingVertex_residue_congr data.Q n m hnm,
    actualPaddingDegreeCut_residue_congr data.Q L n m hnm]

end ProhibitedPrimeFamily

theorem ModFiveThetaInput.actual_family_padding_bin_square (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L η c : ℝ) (h J M B : ℕ)
      (data : ProhibitedPrimeFamily h J M), data.Q = paddingPrimeSupply E L →
      ∀ (site : ℤ) (bins : Finset ℤ), 1 ≤ L → 0 < η → η ≤ 1 →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
        (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      (data.residueLaw B hB).average (fun x =>
        (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2 *
          ∑ j ∈ bins, (paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
            (actualPaddingVertex data.Q) (data.residueOrigin x + site)) ^ 2) /
              paddingTiltNormalizer data.Q ≤ C / L := by
  obtain ⟨C, hC, hb⟩ := hP.actual_padding_residue_bin_square E
  refine ⟨C, hC, ?_⟩
  intro L η c h J M B data hQ site bins hL hη hηone hB D hD
  rw [data.residue_average_padding_squares hB D hD site η c bins]
  have hbQ : ∀ (Q : Finset ℕ), Q = paddingPrimeSupply E L →
      ∀ (hprime : ∀ p ∈ Q, p.Prime) (hQB : ∀ p ∈ Q, p ≤ B)
        (N : (Q → Fin B) → ℤ),
      (∀ z (p : Q), (N z : ZMod p.val) =
        ((z p).val : ZMod p.val) + (site : ZMod p.val)) →
      D ⊆ retainedPrimeDivisors Q →
      (FiniteLaw.independent (fun p : Q => uniformResidueLaw B p.val
        (hprime p p.property).pos (hQB p p.property))).average (fun z =>
          (actualPaddingVertex Q (N z)) ^ 2 * ∑ j ∈ bins,
            (paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
              (actualPaddingVertex Q) (N z)) ^ 2) / paddingTiltNormalizer Q ≤ C / L := by
    intro Q hQ hprime hQB N hN hD
    subst Q
    exact hb L η c B site bins hL hη hηone hQB D hD N hN
  apply hbQ data.Q hQ data.primeQ (fun p hp => hB p (mem_union_right _ hp))
    (fun z => data.paddingResidueOrigin z + site) _ hD
  intro z p
  rw [Int.cast_add, data.paddingResidueOrigin_spec z p]

theorem ModFiveThetaInput.eventually_actual_family_padding_degree_tail
    (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ),
      (data.residueLaw B hB).average (fun x =>
        (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2 *
          if ¬actualPaddingDegreeCut data.Q L (data.residueOrigin x + site) then 1 else 0) /
            paddingTiltNormalizer data.Q ≤ L ^ (-100 : ℝ) := by
  filter_upwards [hP.eventually_actual_padding_degree_tail E] with L hb
  intro h J M B data hQ hB site
  rw [data.residue_average_padding_degree_tail hB site L]
  have hbQ : ∀ (Q : Finset ℕ), Q = paddingPrimeSupply E L →
      ∀ (hprime : ∀ p ∈ Q, p.Prime) (hQB : ∀ p ∈ Q, p ≤ B)
        (N : (Q → Fin B) → ℤ),
      (∀ z (p : Q), (N z : ZMod p.val) =
        ((z p).val : ZMod p.val) + (site : ZMod p.val)) →
      (FiniteLaw.independent (fun p : Q => uniformResidueLaw B p.val
        (hprime p p.property).pos (hQB p p.property))).average (fun z =>
          (actualPaddingVertex Q (N z)) ^ 2 *
            if ¬actualPaddingDegreeCut Q L (N z) then 1 else 0) /
              paddingTiltNormalizer Q ≤ L ^ (-100 : ℝ) := by
    intro Q hQ hprime hQB N hN
    subst Q
    exact hb B site hQB N hN
  apply hbQ data.Q hQ data.primeQ (fun p hp => hB p (mem_union_right _ hp))
    (fun z => data.paddingResidueOrigin z + site)
  intro z p
  rw [Int.cast_add, data.paddingResidueOrigin_spec z p]

end TwoPointCorrelations

end OAI
