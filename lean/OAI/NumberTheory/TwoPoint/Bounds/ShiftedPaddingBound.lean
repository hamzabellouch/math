import OAI.NumberTheory.TwoPoint.Bounds.ShiftedPaddingComparison

namespace OAI

/-! The literal padding deletion bound when each product bin has its
own averaging interval. The product-model cost is paid only once. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_shifted_padding_deletion_uniform
    (hBr : BravermanDepth22Input) (hP : ModFiveThetaInput) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ E : Finset ℕ,
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (P : Fin J → Finset ℕ), primeTuplePool P = data.P →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) → (J : ℝ) ≤ L ^ 2 →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors P →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ Q, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η K : ℝ) (c : ℕ → ℝ), 0 < η → η ≤ 1 → 0 < K →
      ∀ (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ),
      (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q, uniformAverage (fun x : Fin (N j) =>
        paddingRejectionAtom data.Q d.primeFactors Q (actualPaddingBin η (c d) j) L K q
          ((a j + x.val : ℤ) + site j d q))) / paddingTiltNormalizer data.Q ≤
        (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * (C / K + L ^ (-100 : ℝ)) +
          (2 * bins.card * D.card * Q.card * Real.exp (-(L ^ 9))) /
            paddingTiltNormalizer data.Q := by
  obtain ⟨A, hA, hc⟩ := hBr.eventually_shifted_padding_comparison
  refine ⟨A, hA, ?_⟩
  intro E
  obtain ⟨C, hC, hm⟩ := hP.eventually_model_tuple_padding_deletion E
  refine ⟨C, hC, ?_⟩
  filter_upwards [hc, hm] with L hc hm
  intro h J M B data hQ hB hpool hBL P hPeq hprime hdisjoint hJ D hD Q hQsub hqdegree
    bins η K c hη hηone hK site a N hN
  have hd (d : ℕ) (hd : d ∈ D) := primeTupleDivisors_arithmetic P hprime hdisjoint (hD hd)
  have he := hc h J M B data hB hpool hBL D
    (fun d hmem => ((hd d hmem).2.2.trans_eq hPeq).trans subset_union_left)
    (fun d hmem => by simpa only [(hd d hmem).2.1] using hJ)
    Q hQsub hqdegree bins η K c site a N hN
  have he' := (abs_le.mp he).2
  have hm' := hm h J M B data hQ hB P hPeq hprime hdisjoint D hD Q hQsub
    bins η K c hη hηone hK 0
  simp only [add_zero] at hm'
  have hS := paddingTiltNormalizer_pos data.Q
  have hx := (div_le_div_iff_of_pos_right hS).mpr he'
  rw [sub_div] at hx
  linarith

theorem BravermanDepth22Input.eventually_shifted_padding_deletion
    (hBr : BravermanDepth22Input) (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ (A : ℕ) (C : ℝ), 1000 ≤ A ∧ 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (P : Fin J → Finset ℕ), primeTuplePool P = data.P →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) → (J : ℝ) ≤ L ^ 2 →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors P →
      ∀ (Q : Finset ℕ), Q ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ Q, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η K : ℝ) (c : ℕ → ℝ), 0 < η → η ≤ 1 → 0 < K →
      ∀ (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ),
      (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      (∑ j ∈ bins, ∑ d ∈ D, ∑ q ∈ Q, uniformAverage (fun x : Fin (N j) =>
        paddingRejectionAtom data.Q d.primeFactors Q (actualPaddingBin η (c d) j) L K q
          ((a j + x.val : ℤ) + site j d q))) / paddingTiltNormalizer data.Q ≤
        (2 : ℝ) ^ J * (∏ j, primeHarmonicMass (P j)) * (C / K + L ^ (-100 : ℝ)) +
          (2 * bins.card * D.card * Q.card * Real.exp (-(L ^ 9))) /
            paddingTiltNormalizer data.Q := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_shifted_padding_deletion_uniform hP
  obtain ⟨C, hC, hb⟩ := hb E
  exact ⟨A, C, hA, hC, hb⟩

end TwoPointCorrelations

end OAI
