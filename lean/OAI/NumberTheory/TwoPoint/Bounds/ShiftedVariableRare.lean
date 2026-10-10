import OAI.NumberTheory.TwoPoint.Bounds.ShiftedRareDeletion

namespace OAI

/-! Sum the canonical rare-site deletion over bins with separately
chosen integer intervals. The polynomial bin count is absorbed by
the proved second-moment rare-event estimate. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_shifted_variable_rare_deletion_uniform
    (hP : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ (h : ℕ) (E : Finset ℕ)
      (hE : ∀ p, p.Prime → p ∣ h → p ∈ E),
      ∀ (W C : ℝ) (hW : 10 ≤ W) (_hC : 0 ≤ C), ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ (bins : Finset ℤ) (eligible : ℤ → ℕ → ℕ → Prop),
      (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
      (bins.card : ℝ) ≤ Real.exp (C * Real.log L) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let M := ⌊100 * Real.log L⌋₊
      ∀ (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ), (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      (∑ j ∈ bins, uniformAverage (fun x : Fin (N j) =>
        shiftedProhibitedRow (canonicalTraceFamily h E W L (eligible j) hL (by linarith) hE)
          ⌊L ^ (1 / 10 : ℝ)⌋₊ (primeTupleDivisors P) (canonicalPairPadding Q M (eligible j))
            (site j) (a j + x.val))) ≤
        Real.exp (-L ^ (9 / 10 : ℝ)) + bins.card * Real.exp (101 * L) * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hP.eventually_shifted_canonical_rare_deletion_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h E hE W C hW hC
  have hb := hb h E hE W C hW hC
  filter_upwards [hb] with L hb
  intro hL η hη hηone bins eligible he hbins
  dsimp only
  intro site a N hN
  by_cases hempty : bins = ∅
  · subst bins
    simp only [sum_empty, card_empty, Nat.cast_zero, zero_mul, add_zero]
    positivity
  let T : ℝ := bins.card
  let cost := fun j : ℤ => uniformAverage (fun x : Fin (N j) =>
    shiftedProhibitedRow (canonicalTraceFamily h E W L (eligible j) hL (by linarith) hE)
      ⌊L ^ (1 / 10 : ℝ)⌋₊
      (primeTupleDivisors (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)))
      (canonicalPairPadding (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊ (eligible j))
      (site j) (a j + x.val))
  have hT : 0 < T := by
    dsimp only [T]
    exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hempty)
  have heach (j : ℤ) (hj : j ∈ bins) : T * cost j ≤
      Real.exp (-L ^ (9 / 10 : ℝ)) + T * Real.exp (101 * L) * Real.exp (-(L ^ 9)) :=
    hb hL η hη hηone (eligible j) (he j hj) T hT.le hbins (site j) (a j) (N j) (hN j hj)
  have hsum : T * (∑ j ∈ bins, cost j) ≤
      T * (Real.exp (-L ^ (9 / 10 : ℝ)) + T * Real.exp (101 * L) * Real.exp (-(L ^ 9))) := by
    rw [mul_sum]
    calc
      _ ≤ ∑ _j ∈ bins, (Real.exp (-L ^ (9 / 10 : ℝ)) +
          T * Real.exp (101 * L) * Real.exp (-(L ^ 9))) := sum_le_sum heach
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; rfl
  exact le_of_mul_le_mul_left hsum hT

theorem ModFiveThetaInput.eventually_shifted_variable_rare_deletion
    (hP : ModFiveThetaInput) (hBr : BravermanDepth22Input)
    (h : ℕ) (E : Finset ℕ) (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (W C : ℝ) (hW : 10 ≤ W) (hC : 0 ≤ C) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ (bins : Finset ℤ) (eligible : ℤ → ℕ → ℕ → Prop),
      (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
      (bins.card : ℝ) ≤ Real.exp (C * Real.log L) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let M := ⌊100 * Real.log L⌋₊
      ∀ (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ), (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      (∑ j ∈ bins, uniformAverage (fun x : Fin (N j) =>
        shiftedProhibitedRow (canonicalTraceFamily h E W L (eligible j) hL (by linarith) hE)
          ⌊L ^ (1 / 10 : ℝ)⌋₊ (primeTupleDivisors P) (canonicalPairPadding Q M (eligible j))
            (site j) (a j + x.val))) ≤
        Real.exp (-L ^ (9 / 10 : ℝ)) + bins.card * Real.exp (101 * L) * Real.exp (-(L ^ 9)) := by
  obtain ⟨A, hA, hb⟩ := hP.eventually_shifted_variable_rare_deletion_uniform hBr
  exact ⟨A, hA, hb h E hE W C hW hC⟩

end TwoPointCorrelations

end OAI
