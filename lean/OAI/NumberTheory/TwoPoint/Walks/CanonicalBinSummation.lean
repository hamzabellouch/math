import OAI.NumberTheory.TwoPoint.Walks.RetainedBinSummation
import OAI.NumberTheory.TwoPoint.Walks.CanonicalRetainedMass

namespace OAI

/-! Sum the actual retained bin correlations, normalized by the exact
retained divisor mass. The input functions may differ from bin to bin. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def canonicalRetainedPrefix (h l b : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (N : ℕ) : ℂ :=
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ data.pairs) z
  retainedPrimePrefix P Q Qp actualPaddingCoefficient (fun d q => (d, q) ∈ data.pairs)
    L (Real.exp (4 * J)) W (fun _ => actualPaddingDegreeCut Qp L)
    h (progressionEdgeGate h l b) keep N

theorem ModFiveThetaInput.eventually_canonical_bin_sum_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (_hl : 0 < l) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ (bins : Finset ℤ) (eligible : ℤ → ℕ → ℕ → Prop),
      (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
      ∀ (b : ℕ) (N : ℤ → ℕ), (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let R := Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      ‖∑ j ∈ bins, canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j)‖ /
        totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
      (6 * bins.card * (l : ℝ) ^ 2 / L) * (R / W ^ J) +
        6 * bins.card * Real.exp (-L) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_actual_retained_bin_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh hl E hE hEl W hW
  have hb := hb h l hh hl E hE hEl W hW
  filter_upwards [hb, hprime.eventually_canonical_retained_mass E W hW] with L hb hm
  intro hL η hη hηone bins eligible he b N hN
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let S := paddingTiltNormalizer (paddingPrimeSupply E L)
  let V := ∏ j, primeHarmonicMass (P j)
  let R := Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  have hmass := hm hL η hη
  have hbound (j : ℤ) (hj : j ∈ bins) :
      ‖canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j)‖ ≤
        3 * (l : ℝ) ^ 2 * S * R / L + 3 * Real.exp (-L) := by
    exact hb hL η hη hηone (eligible j) (he j hj) b (N j) (hN j hj)
  exact retained_bin_sum_mass_lower bins
    (fun j => canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j))
    S V (totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η)
    L l R (Real.exp (-L)) W J (paddingTiltNormalizer_one_le _) hW hmass.1
    (by linarith) hmass.2 (by positivity) (Real.exp_pos _).le hbound

theorem ModFiveThetaInput.eventually_canonical_bin_sum
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input)
    (h l : ℕ) (hh : 0 < h) (hl : 0 < l) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ (bins : Finset ℤ) (eligible : ℤ → ℕ → ℕ → Prop),
      (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
      ∀ (b : ℕ) (N : ℤ → ℕ), (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let R := Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      ‖∑ j ∈ bins, canonicalRetainedPrefix h l b E W L (eligible j) hL hW hE (N j)‖ /
        totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
      (6 * bins.card * (l : ℝ) ^ 2 / L) * (R / W ^ J) +
        6 * bins.card * Real.exp (-L) := by
  obtain ⟨A, hA, hbound⟩ := hprime.eventually_canonical_bin_sum_uniform hBr
  exact ⟨A, hA, hbound h l hh hl E hE hEl W hW⟩

end TwoPointCorrelations

end OAI
