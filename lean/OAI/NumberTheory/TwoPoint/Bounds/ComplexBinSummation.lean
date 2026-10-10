import OAI.NumberTheory.TwoPoint.Bounds.ComplexBinGeometry
import OAI.NumberTheory.TwoPoint.Walks.CanonicalRetainedMass
import OAI.NumberTheory.TwoPoint.Walks.RetainedBinSummation

namespace OAI

/-! Sum arbitrary complex directed bins against their actual reciprocal divisor mass. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

noncomputable def canonicalComplexPrefix (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (F G : ℤ → ℂ) (N : ℕ) : ℂ :=
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let active := fun d q => (d, q) ∈ data.pairs
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ active z
  retainedComplexPrefix P Q Qp actualPaddingCoefficient active L (Real.exp (4 * J)) W
    (fun _ => actualPaddingDegreeCut Qp L) h (fun _ _ _ => True) keep F G N

theorem ModFiveThetaInput.eventually_canonical_complex_bin_sum
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h : ℕ) (_hh : 0 < h) (E : Finset ℕ)
        (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 → Real.exp η < 2 →
      ∀ (bins : Finset ℤ) (eligible : ℤ → ℕ → ℕ → Prop),
        (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
        (∀ j ∈ bins, ∀ d q, eligible j d q → 0 < d ∧ 0 < q) →
        (∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (Real.log d) j q) →
      ∀ (F G : ℤ → ℂ), (∀ n, ‖F n‖ ≤ 1) → (∀ n, ‖G n‖ ≤ 1) →
      ∀ (N : ℤ → ℕ) (v : ℤ → ℂ),
        (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
        (∀ j ∈ bins, ‖v j‖ ≤ 1) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let R := Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      ‖∑ j ∈ bins, v j * canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j)‖ /
        totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η ≤
        (480 * bins.card / L) * (R / W ^ J) + 480 * bins.card * Real.exp (-L) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_canonical_complex_bin hBr
  refine ⟨A, hA, ?_⟩
  intro h hh E hE W hW
  filter_upwards [hb h hh E hE W hW, hprime.eventually_canonical_retained_mass E W hW]
    with L hb hm
  intro hL η hη hηone hηtwo bins eligible he hpos hbin F G hF hG N v hN hv
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let S := paddingTiltNormalizer (paddingPrimeSupply E L)
  let V := ∏ j, primeHarmonicMass (P j)
  let R := Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  have hmass := hm hL η hη
  have hbound (j : ℤ) (hj : j ∈ bins) :
      ‖v j * canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j)‖ ≤
        3 * (1 : ℝ) ^ 2 * S * (80 * R) / L + 3 * (80 * Real.exp (-L)) := by
    have hs : ∀ d q, eligible j d q →
        logBinStep h η j ≤ (h * q * d : ℕ) ∧
          (h * q * d : ℕ) < 2 * logBinStep h η j := by
      intro d q hdq
      exact actualPaddingBin_short_shift h d q hh (hpos j hj d q hdq).1
        (hpos j hj d q hdq).2 η hηtwo j (hbin j hj d q hdq)
    have ht := hb hL η hη hηone (eligible j) (he j hj)
      (logBinStep h η j) (logBinStep_pos h hh η j) hs F G hF hG (N j) (hN j hj)
    have hnorm : ‖v j * canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j)‖ ≤
        ‖canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hv j hj)
    have hval : ‖canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j)‖ ≤
        240 * S * R / L + 240 * Real.exp (-L) := ht
    apply (hnorm.trans hval).trans_eq
    ring
  have hr := retained_bin_sum_mass_lower bins
    (fun j => v j * canonicalComplexPrefix h E W L (eligible j) hL hW hE F G (N j))
    S V (totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η)
    L 1 (80 * R) (80 * Real.exp (-L)) W J (paddingTiltNormalizer_one_le _) hW
    hmass.1 (by linarith) hmass.2 (by positivity) (by positivity) hbound
  convert hr using 1; ring

end TwoPointCorrelations

end OAI
