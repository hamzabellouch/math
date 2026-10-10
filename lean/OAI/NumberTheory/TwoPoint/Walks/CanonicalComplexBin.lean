import OAI.NumberTheory.TwoPoint.Walks.CanonicalComplexPrefix
import OAI.NumberTheory.TwoPoint.Walks.RetainedBoundaryScale

namespace OAI

/-! A short-range retained complex bin has the same decay as a Liouville bin. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma complex_block_test_normalization (L K T G R S M δ : ℝ)
    (hL : L ≠ 0) (hM : M ≠ 0) :
    (40 * ((3 * R) * (2 * M * S) + (M * (2 * K * T) * G) * δ)) / (L * M) =
      240 * S * R / L + 80 * (K / L * G * T) * δ := by
  field_simp
  ring

theorem ModFiveThetaInput.eventually_canonical_complex_bin
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h : ℕ) (_hh : 0 < h) (E : Finset ℕ)
        (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      ∀ (D : ℤ), 0 < D →
      (∀ d q, eligible d q → D ≤ (h * q * d : ℕ) ∧ (h * q * d : ℕ) < 2 * D) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let active := fun d q => (d, q) ∈ data.pairs
      let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ active z
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      ∀ (F G : ℤ → ℂ), (∀ n, ‖F n‖ ≤ 1) → (∀ n, ‖G n‖ ≤ 1) →
      ∀ N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      ‖retainedComplexPrefix P Q Qp actualPaddingCoefficient active L K W
        (fun _ => actualPaddingDegreeCut Qp L) h (fun _ _ _ => True) keep F G N‖ ≤
        240 * paddingTiltNormalizer Qp * R / L + 240 * Real.exp (-L) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_canonical_complex_prefix hBr
  refine ⟨A, hA, ?_⟩
  intro h hh E hE W hW
  filter_upwards [hb h hh E hE W hW, eventually_retained_row_scale W hW,
    eventually_const_le_exp_quarter h, eventually_ge_atTop (212 : ℝ)]
    with L hb hrow hhsize hlarge
  intro hL η hη hηone eligible he D hD hs
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let active := fun d q => (d, q) ∈ data.pairs
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ active z
  let M := ⌈Real.exp (103 * L)⌉₊
  let K := Real.exp (4 * J)
  let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  let C := K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J
  intro F G hF hG N hN
  have hLp : 0 < L := by linarith
  have hMp : (0 : ℝ) < M := lt_of_lt_of_le (Real.exp_pos _) (Nat.le_ceil _)
  have hMlo : Real.exp (103 * L) ≤ (M : ℝ) := Nat.le_ceil _
  have hMhi : (M : ℝ) ≤ 2 * Real.exp (103 * L) := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ Real.exp (103 * L) from (Real.exp_pos _).le)
    have hex : 1 ≤ Real.exp (103 * L) := Real.one_le_exp (by linarith)
    dsimp only [M]
    linarith
  have hNlarge : Real.exp (106 * L) ≤ (N : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hN
    have hp : L ^ 2 ≤ L ^ A := pow_le_pow_right₀ hL (by omega)
    nlinarith
  have hC0 : 0 ≤ C := by dsimp [C, K]; positivity
  have herr := retained_boundary_error_bound L C h 1 M N (by linarith)
    hC0 (Nat.cast_nonneg _) (by norm_num) hrow hhsize
    (Real.one_le_exp (by linarith)) hMlo hMhi hNlarge
  have hf : ((h * ⌊Real.exp (100 * L + 1)⌋₊ : ℕ) : ℝ) ≤
      (h : ℝ) * Real.exp (100 * L + 1) := by
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.exp_pos _).le) (Nat.cast_nonneg _)
  have hboundary : ((h * ⌊Real.exp (100 * L + 1)⌋₊ : ℕ) : ℝ) / M * C ≤
      ((h : ℝ) * Real.exp (100 * L + 1)) / M * C := by gcongr
  have ht := hb hL η hη hηone eligible he D hD hs F G hF hG N hN
  have hnorm := complex_block_test_normalization L K ((8 * W) ^ J)
    ((5 : ℝ) ^ (400 * Real.log L)) R (paddingTiltNormalizer Qp) M
    (Real.exp (-(2 * ⌊L⌋₊ : ℕ))) hLp.ne' hMp.ne'
  rw [hnorm] at ht
  have hsecond : 0 ≤ ((h : ℝ) * Real.exp (100 * L + 1)) / M * C := by positivity
  have hthird : 0 ≤ 2 * (M : ℝ) / N * C := by positivity
  simp only [one_mul] at herr
  change C * Real.exp (-(2 * ⌊L⌋₊ : ℕ)) +
    ((h : ℝ) * Real.exp (100 * L + 1)) / M * C + 2 * (M : ℝ) / N * C ≤
      3 * Real.exp (-L) at herr
  change ‖retainedComplexPrefix P Q Qp actualPaddingCoefficient active L K W
    (fun _ => actualPaddingDegreeCut Qp L) h (fun _ _ _ => True) keep F G N‖ ≤ _
  change ‖retainedComplexPrefix P Q Qp actualPaddingCoefficient active L K W
    (fun _ => actualPaddingDegreeCut Qp L) h (fun _ _ _ => True) keep F G N‖ ≤
    240 * paddingTiltNormalizer Qp * R / L + 80 * C * Real.exp (-(2 * ⌊L⌋₊ : ℕ)) +
    ((h * ⌊Real.exp (100 * L + 1)⌋₊ : ℕ) : ℝ) / M * C + 2 * (M : ℝ) / N * C at ht
  nlinarith

end TwoPointCorrelations

end OAI
