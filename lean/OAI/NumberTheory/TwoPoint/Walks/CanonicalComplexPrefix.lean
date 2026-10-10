import OAI.NumberTheory.TwoPoint.Walks.CanonicalComplexTesting
import OAI.NumberTheory.TwoPoint.Bounds.ComplexPrefixBound

namespace OAI

/-! Canonical directed complex prefix estimate with all boundary terms explicit. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_canonical_complex_prefix
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
      let M := ⌈Real.exp (103 * L)⌉₊
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      ∀ (F G : ℤ → ℂ), (∀ n, ‖F n‖ ≤ 1) → (∀ n, ‖G n‖ ≤ 1) →
      ∀ N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      ‖retainedComplexPrefix P Q Qp actualPaddingCoefficient active L K W
        (fun _ => actualPaddingDegreeCut Qp L) h (fun _ _ _ => True) keep F G N‖ ≤
        (40 * ((3 * R) * (2 * M * paddingTiltNormalizer Qp) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ)))) / (L * M) +
        ((h * ⌊Real.exp (100 * L + 1)⌋₊ : ℕ) : ℝ) / M *
          (K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J) +
        2 * (M : ℝ) / N * (K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_canonical_complex_blocks hBr
  refine ⟨A, hA, ?_⟩
  intro h hh E hE W hW
  filter_upwards [hb h hh E hE W hW, hprime.eventually_actual_pool_masses E W hW]
    with L hb hmass
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
  intro F G hF hG N hN
  have hNp : 0 < N := by exact_mod_cast (Real.exp_pos _).trans_le hN
  have hMp : 0 < M := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  have hp := centeredPrimeBands_prime E (L ^ (199 / 200 : ℝ)) W J
  have hd := centeredPrimeBands_disjoint E (L ^ (199 / 200 : ℝ)) W J
    (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hstep (e : ((j : Fin J) → P j) × Q) :
      retainedPrimeStep active h e ≤ h * ⌊Real.exp (100 * L + 1)⌋₊ := by
    apply retainedPrimeStep_le h hη hηone
    intro d q hmem
    exact he d q (canonicalTraceFamily_pair_eligible h E W L eligible hL hW hE d q hmem)
  have ht := hb hL η hη hηone eligible he D hD hs F G hF hG N hN
  exact retainedComplexPrefix_bound P hp hd M (h * ⌊Real.exp (100 * L + 1)⌋₊) N
    Q Qp actualPaddingCoefficient active L K W (fun _ => actualPaddingDegreeCut Qp L)
    h (fun _ _ _ => True) keep F G hF hG hMp hNp (by linarith) (Real.exp_pos _).le
    (by linarith) (fun q _ => actualPaddingCoefficient_nonneg q)
    (fun j => (hmass.2.1 j).2.1) hstep _ ht

end TwoPointCorrelations

end OAI
