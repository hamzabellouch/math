import OAI.NumberTheory.TwoPoint.Bounds.StateCostComparison
import OAI.NumberTheory.TwoPoint.Bounds.DegreeCostComparison
import OAI.NumberTheory.TwoPoint.Bounds.PaddingDeletionIdentity
import OAI.NumberTheory.TwoPoint.Bounds.PrimeRowSecondMoment

namespace OAI

/-! Compare the two disjoint padding failures before summing pairs.
The model side is exactly the rejected padding mass. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma uniformFiniteLaw_sum_error {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] (μ : FiniteLaw β)
    (f : ι → α → ℝ) (g : ι → β → ℝ) (ε : ι → ℝ)
    (h : ∀ i, |uniformAverage (f i) - μ.average (g i)| ≤ ε i) :
    |uniformAverage (fun x => ∑ i, f i x) - μ.average (fun y => ∑ i, g i y)| ≤ ∑ i, ε i := by
  rw [uniformAverage_sum, μ.average_sum, ← sum_sub_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun i _ => h i))

theorem BravermanDepth22Input.eventually_padding_atom_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P ∪ data.Q → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (q : ℕ), q ∈ retainedPrimeDivisors data.Q →
      (q.primeFactors.card : ℝ) ≤ 100 * Real.log L →
      ∀ (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      ∀ (eligible : ℕ → Prop) (K : ℝ) (site : ℤ) (a N : ℕ),
      Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      |uniformAverage (fun x : Fin N =>
          paddingRejectionAtom data.Q S D eligible L K q ((a + x.val : ℤ) + site)) -
        (data.residueLaw B hB).average (fun x =>
          paddingRejectionAtom data.Q S D eligible L K q (data.residueOrigin x + site))| ≤
            2 * Real.exp (-(L ^ 9)) := by
  obtain ⟨A₁, hA₁, hd⟩ := hBr.eventually_degree_cost_comparison
  obtain ⟨A₂, hA₂, hs⟩ := hBr.eventually_density_cost_comparison
  refine ⟨A₁ + A₂, by omega, ?_⟩
  filter_upwards [hd, hs, eventually_ge_atTop (1 : ℝ)] with L hd hs hL
  intro h J M B data hB hpool hBL S hS hSL q hq hqdegree D hD eligible K site a N hN
  have hN₁ : Real.exp (L ^ A₁ / 2) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hL (Nat.le_add_right A₁ A₂)) (by norm_num))).trans hN
  have hN₂ : Real.exp (L ^ A₂ / 2) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hL (Nat.le_add_left A₂ A₁)) (by norm_num))).trans hN
  by_cases he : eligible q
  · let H := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S n *
        if (q : ℤ) ∣ n ∧ 400 * Real.log L < (actualPaddingDegree data.Q n : ℝ) then 1 else 0
    let G := fun n : ℤ => actualPaddingCoefficient q * positivePrimeWeight S n *
        if (q : ℤ) ∣ n ∧ actualPaddingDegreeCut data.Q L n ∧
          K / L < paddingDensity D actualPaddingCoefficient eligible (actualPaddingVertex data.Q) n
          then 1 else 0
    have hlog : 0 ≤ 400 * Real.log L := mul_nonneg (by norm_num) (Real.log_nonneg hL)
    have hH := hd h J M B data hB hpool hBL S data.Q hS subset_union_right hSL
      q hq hqdegree (400 * Real.log L) hlog le_rfl site a N hN₁
    have hG := hs h J M B data hB hpool hBL S hS hSL q hq hqdegree D hD eligible K site a N hN₂
    have hsplit (n : ℤ) : paddingRejectionAtom data.Q S D eligible L K q n = H n + G n := by
      simp only [paddingRejectionAtom, he, ite_true, padding_rejection_failure_split, mul_add, H, G]
    simp_rw [hsplit]
    have hu : uniformAverage (fun x : Fin N => H ((a + x.val : ℤ) + site) +
        G ((a + x.val : ℤ) + site)) =
        uniformAverage (fun x : Fin N => H ((a + x.val : ℤ) + site)) +
        uniformAverage (fun x : Fin N => G ((a + x.val : ℤ) + site)) := by
      simp only [uniformAverage, sum_add_distrib, add_div]
    rw [hu, (data.residueLaw B hB).average_add]
    calc
      _ = |(uniformAverage (fun x : Fin N => H ((a + x.val : ℤ) + site)) -
          (data.residueLaw B hB).average (fun x => H (data.residueOrigin x + site))) +
          (uniformAverage (fun x : Fin N => G ((a + x.val : ℤ) + site)) -
          (data.residueLaw B hB).average (fun x => G (data.residueOrigin x + site)))| := by
            congr 1
            ring
      _ ≤ _ := (abs_add_le _ _).trans (show _ ≤ 2 * Real.exp (-(L ^ 9)) by linarith [hH, hG])
  · simp only [paddingRejectionAtom, he, ite_false, uniformAverage, sum_const_zero,
      zero_div, (data.residueLaw B hB).average_const, sub_self, abs_zero]
    positivity

theorem BravermanDepth22Input.eventually_padding_mass_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M)
        (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P ∪ data.Q → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ D, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η c K : ℝ) (site : ℤ) (a N : ℕ),
      Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun n : ℤ => positivePrimeWeight S n * paddingRejectedMass data.Q D bins η c L K n
      |uniformAverage (fun x : Fin N => F ((a + x.val : ℤ) + site)) -
        (data.residueLaw B hB).average (fun x => F (data.residueOrigin x + site))| ≤
          2 * bins.card * D.card * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hBr.eventually_padding_atom_comparison
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with L hb
  intro h J M B data hB hpool hBL S hS hSL D hD hdegree bins η c K site a N hN
  dsimp only
  simp_rw [padding_rejection_bin_identity]
  have he (j : bins) :
      |uniformAverage (fun x : Fin N => ∑ q : D,
          paddingRejectionAtom data.Q S D (actualPaddingBin η c j.val) L K q.val
            ((a + x.val : ℤ) + site)) -
        (data.residueLaw B hB).average (fun x => ∑ q : D,
          paddingRejectionAtom data.Q S D (actualPaddingBin η c j.val) L K q.val
            (data.residueOrigin x + site))| ≤ D.card * (2 * Real.exp (-(L ^ 9))) := by
    simpa only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul] using
      uniformFiniteLaw_sum_error (data.residueLaw B hB)
        (fun (q : D) (x : Fin N) => paddingRejectionAtom data.Q S D (actualPaddingBin η c j.val)
          L K q.val ((a + x.val : ℤ) + site))
        (fun (q : D) x => paddingRejectionAtom data.Q S D (actualPaddingBin η c j.val)
          L K q.val (data.residueOrigin x + site)) (fun _ => 2 * Real.exp (-(L ^ 9)))
        (fun q => hb h J M B data hB hpool hBL S hS hSL q.val (hD q.property)
          (hdegree q.val q.property) D hD (actualPaddingBin η c j.val) K site a N hN)
  simp_rw [← sum_coe_sort D, ← sum_coe_sort bins]
  have ht := uniformFiniteLaw_sum_error (data.residueLaw B hB)
    (fun (j : bins) (x : Fin N) => ∑ q : D,
      paddingRejectionAtom data.Q S D (actualPaddingBin η c j.val) L K q.val ((a + x.val : ℤ) + site))
    (fun (j : bins) x => ∑ q : D,
      paddingRejectionAtom data.Q S D (actualPaddingBin η c j.val) L K q.val (data.residueOrigin x + site))
    (fun _ => D.card * (2 * Real.exp (-(L ^ 9)))) he
  convert ht using 1
  simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]
  ring

theorem BravermanDepth22Input.eventually_integer_padding_deletion
    (hBr : BravermanDepth22Input) (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ (A : ℕ) (C : ℝ), 1000 ≤ A ∧ 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (h J M B : ℕ) (data : ProhibitedPrimeFamily h J M),
      data.Q = paddingPrimeSupply E L →
      ∀ (_hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.P ∪ data.Q).Nonempty → (B : ℝ) ≤ Real.exp L →
      ∀ (S : Finset ℕ), S ⊆ data.P → (S.card : ℝ) ≤ L ^ 2 →
      ∀ (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      (∀ q ∈ D, (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) →
      ∀ (bins : Finset ℤ) (η c K : ℝ), 0 < η → η ≤ 1 → 0 < K →
      ∀ (site : ℤ) (a N : ℕ), Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => positivePrimeWeight S ((a + x.val : ℤ) + site) *
        paddingRejectedMass data.Q D bins η c L K ((a + x.val : ℤ) + site)) /
          paddingTiltNormalizer data.Q ≤
        positivePrimeNormalizer S * (C / K + L ^ (-100 : ℝ)) +
          (2 * bins.card * D.card * Real.exp (-(L ^ 9))) / paddingTiltNormalizer data.Q := by
  obtain ⟨A, hA, hc⟩ := hBr.eventually_padding_mass_comparison
  obtain ⟨C, hC, hp⟩ := hP.eventually_positive_padding_cut_cost E
  refine ⟨A, C, hA, hC, ?_⟩
  filter_upwards [hc, hp] with L hc hp
  intro h J M B data hQ hB hpool hBL S hSP hSL D hD hdegree bins η c K hη hηone hK site a N hN
  have hcomp := hc h J M B data hB hpool hBL S (hSP.trans subset_union_left) hSL
    D hD hdegree bins η c K site a N hN
  have hmodel := hp η c K h J M B data hQ hB site bins hη hηone hK D hD S hSP
  have hdiff := (le_abs_self _).trans hcomp
  dsimp only at hdiff
  calc
    _ ≤ ((data.residueLaw B hB).average (fun x =>
          positivePrimeWeight S (data.residueOrigin x + site) *
            paddingRejectedMass data.Q D bins η c L K (data.residueOrigin x + site)) +
          2 * bins.card * D.card * Real.exp (-(L ^ 9))) / paddingTiltNormalizer data.Q :=
      div_le_div_of_nonneg_right (by linarith) (paddingTiltNormalizer_pos data.Q).le
    _ = _ := add_div _ _ _
    _ ≤ _ := by linarith

end TwoPointCorrelations

end OAI
