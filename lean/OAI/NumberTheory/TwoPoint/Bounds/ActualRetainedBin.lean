import OAI.NumberTheory.TwoPoint.Bounds.ActualRetainedPrefix
import OAI.NumberTheory.TwoPoint.Walks.RetainedBoundaryScale
import OAI.NumberTheory.TwoPoint.Walks.BlockTestNormalization

namespace OAI

/-! The canonical retained-bin estimate: spectral main term plus an
exponentially small error, uniformly in the bin and progression class. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_actual_retained_bin_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (_hl : 0 < l) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) z
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      ∀ b N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      ‖retainedPrimePrefix P Q Qp actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
        h (progressionEdgeGate h l b) keep N‖ ≤
      3 * (l : ℝ) ^ 2 * paddingTiltNormalizer Qp * R / L + 3 * Real.exp (-L) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_actual_retained_prefix_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh hl E hE hEl W hW
  have hb := hb h l hh hl E hE hEl W hW
  filter_upwards [hb, eventually_retained_row_scale W hW,
    eventually_const_le_exp_quarter h, eventually_const_le_exp_quarter l,
    eventually_ge_atTop (212 : ℝ)] with L hb hrow hhsize hlsize hlarge
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ data.pairs) z
  let K := Real.exp (4 * J)
  let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  let M := ⌈Real.exp (103 * L)⌉₊
  let D := K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J
  intro b N hN
  have hLp : 0 < L := by linarith
  have hMp : (0 : ℝ) < M := lt_of_lt_of_le (Real.exp_pos _) (Nat.le_ceil _)
  have hMlo : Real.exp (103 * L) ≤ (M : ℝ) := Nat.le_ceil _
  have hMhi : (M : ℝ) ≤ 2 * Real.exp (103 * L) := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.exp (103 * L) from (Real.exp_pos _).le)
    have he : 1 ≤ Real.exp (103 * L) := Real.one_le_exp (by linarith)
    dsimp only [M]
    linarith
  have hNlarge : Real.exp (106 * L) ≤ (N : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hN
    have hp : L ^ 2 ≤ L ^ A := pow_le_pow_right₀ hL (by omega)
    nlinarith
  have herr := retained_boundary_error_bound L D h l M N (by linarith)
    (by dsimp [D, K]; positivity) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hrow hhsize hlsize hMlo hMhi hNlarge
  have hf : ((h * ⌊Real.exp (100 * L + 1)⌋₊ : ℕ) : ℝ) ≤
      (h : ℝ) * Real.exp (100 * L + 1) := by
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.exp_pos _).le) (Nat.cast_nonneg _)
  have hboundary : ((h * ⌊Real.exp (100 * L + 1)⌋₊ : ℕ) : ℝ) / M * D ≤
      ((h : ℝ) * Real.exp (100 * L + 1)) / M * D := by
    gcongr
  have ht := hb hL η hη hηone eligible he b N hN
  have hnorm := block_test_normalization L K ((8 * W) ^ J)
    ((5 : ℝ) ^ (400 * Real.log L)) R (paddingTiltNormalizer Qp) M l
    (Real.exp (-(2 * ⌊L⌋₊ : ℕ))) hLp.ne' hMp.ne'
  change ‖retainedPrimePrefix P Q Qp actualPaddingCoefficient
    (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
    h (progressionEdgeGate h l b) keep N‖ ≤ _
  change ‖retainedPrimePrefix P Q Qp actualPaddingCoefficient
    (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
    h (progressionEdgeGate h l b) keep N‖ ≤ _ at ht
  rw [hnorm] at ht
  change _ + _ + _ ≤ 3 * Real.exp (-L) at herr
  dsimp only [D] at herr hboundary
  linarith

theorem ModFiveThetaInput.eventually_actual_retained_bin
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input)
    (h l : ℕ) (hh : 0 < h) (hl : 0 < l) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) z
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      ∀ b N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      ‖retainedPrimePrefix P Q Qp actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
        h (progressionEdgeGate h l b) keep N‖ ≤
      3 * (l : ℝ) ^ 2 * paddingTiltNormalizer Qp * R / L + 3 * Real.exp (-L) := by
  obtain ⟨A, hA, hbound⟩ := hprime.eventually_actual_retained_bin_uniform hBr
  exact ⟨A, hA, hbound h l hh hl E hE hEl W hW⟩

end TwoPointCorrelations

end OAI
