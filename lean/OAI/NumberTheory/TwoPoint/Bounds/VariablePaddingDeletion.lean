import OAI.NumberTheory.TwoPoint.Bounds.VariableWindowComparison
import OAI.NumberTheory.TwoPoint.Walks.TuplePaddingDeletion

namespace OAI

/-! Padding deletion with the bin-dependent integer interval lengths
used in the manuscript. The product model is summed only after each
bin has been transferred separately. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_variable_padding_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (D : Finset ℕ),
      (∀ d ∈ D, d.primeFactors ⊆ data.P ∪ data.Q) →
      (∀ d ∈ D, (d.primeFactors.card : ℝ) ≤ L ^ 2) →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ Q, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η K : ℝ) (c : ℕ → ℝ) (site : ℤ) (a N : ℤ → ℕ),
      (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      |(∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q, uniformAverage (fun x : Fin (N j) =>
          paddingRejectionAtom data.Q d.primeFactors Q (actualPaddingBin η (c d) j) L K q
            ((a j + x.val : ℤ) + site))) -
        (data.residueLaw B hB).average (fun x => ∑ d ∈ D,
          positivePrimeWeight d.primeFactors (data.residueOrigin x + site) *
            paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x + site))| ≤
        2 * bins.card * D.card * Q.card * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_padding_atom_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL D hD hcard Q hQ hqdegree bins η K c site a N hN
  let I := bins ×ˢ (D ×ˢ Q)
  let f := fun (i : ℤ × (ℕ × ℕ)) (n : ℤ) =>
    paddingRejectionAtom data.Q i.2.1.primeFactors Q (actualPaddingBin η (c i.2.1) i.1)
      L K i.2.2 (n + site)
  let g := fun (i : ℤ × (ℕ × ℕ)) (x : ↥(data.P ∪ data.Q) → Fin B) => f i (data.residueOrigin x)
  have hs := finite_interval_family_error I (data.residueLaw B hB)
    (fun i => a i.1) (fun i => N i.1) f g (fun _ => 2 * Real.exp (-(L ^ 9))) (by
      intro i hi
      obtain ⟨hj, hdq⟩ := mem_product.mp hi
      obtain ⟨hd, hq⟩ := mem_product.mp hdq
      exact hb h J M B data hB hpool hBL i.2.1.primeFactors (hD _ hd) (hcard _ hd)
        i.2.2 (hQ hq) (hqdegree _ hq) Q hQ (actualPaddingBin η (c i.2.1) i.1)
        K site (a i.1) (N i.1) (hN _ hj))
  have he : (∑ _i ∈ I, 2 * Real.exp (-(L ^ 9))) =
      2 * bins.card * D.card * Q.card * Real.exp (-(L ^ 9)) := by
    simp only [sum_const, nsmul_eq_mul, I, card_product, Nat.cast_mul]
    ring
  rw [he] at hs
  simp only [I, sum_product, f, g] at hs
  have hmodel (x : ↥(data.P ∪ data.Q) → Fin B) :
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q,
        paddingRejectionAtom data.Q d.primeFactors Q (actualPaddingBin η (c d) j) L K q
          (data.residueOrigin x + site)) =
      ∑ d ∈ D, positivePrimeWeight d.primeFactors (data.residueOrigin x + site) *
        paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x + site) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro d _
    exact (padding_rejection_bin_identity data.Q d.primeFactors Q bins η (c d) L K _).symm
  simpa only [hmodel] using hs

theorem ModFiveThetaInput.eventually_model_tuple_padding_deletion
    (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      ∀ (P : Fin J → Finset ℕ), primeTuplePool P = data.P →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors P →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      ∀ (bins : Finset ℤ) (η K : ℝ) (c : ℕ → ℝ), 0 < η → η ≤ 1 → 0 < K → ∀ site : ℤ,
      (data.residueLaw B hB).average (fun x => ∑ d ∈ D,
        positivePrimeWeight d.primeFactors (data.residueOrigin x + site) *
          paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x + site)) /
            paddingTiltNormalizer data.Q ≤
      (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * (C / K + L ^ (-100 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := hP.eventually_positive_padding_cut_cost E
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hb hL
  intro h J M B data hQ hB P hPeq hprime hdisjoint D hD Q hQsub bins η K c hη hηone hK site
  have heach (d : ℕ) (hmem : d ∈ D) :
      (data.residueLaw B hB).average (fun x =>
        positivePrimeWeight d.primeFactors (data.residueOrigin x + site) *
          paddingRejectedMass data.Q Q bins η (c d) L K (data.residueOrigin x + site)) /
            paddingTiltNormalizer data.Q ≤
      positivePrimeNormalizer d.primeFactors * (C / K + L ^ (-100 : ℝ)) := by
    have hd := primeTupleDivisors_arithmetic P hprime hdisjoint (hD hmem)
    exact hb η (c d) K h J M B data hQ hB site bins hη hηone hK Q hQsub
      d.primeFactors (hd.2.2.trans_eq hPeq)
  rw [(data.residueLaw B hB).average_finset_sum, sum_div]
  calc
    _ ≤ ∑ d ∈ D, positivePrimeNormalizer d.primeFactors * (C / K + L ^ (-100 : ℝ)) :=
      sum_le_sum heach
    _ = (∑ d ∈ D, positivePrimeNormalizer d.primeFactors) * (C / K + L ^ (-100 : ℝ)) :=
      (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (tuple_normalizer_sum_le P hprime hdisjoint D hD)
      (add_nonneg (div_nonneg hC.le hK.le) (Real.rpow_nonneg (by linarith) _))

end TwoPointCorrelations

end OAI
