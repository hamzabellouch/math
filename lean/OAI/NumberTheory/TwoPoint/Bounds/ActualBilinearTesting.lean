import OAI.NumberTheory.TwoPoint.Bounds.ActualAffineTesting
import OAI.NumberTheory.TwoPoint.Bounds.PaddingPolarization

namespace OAI

/-! Two bounded sequences in the already-proved canonical graph estimate. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_actual_affine_bilinear_testing
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
      ∀ gate : ℕ → ℤ → ℤ → Prop, (∀ d n m, gate d n m ↔ gate d m n) →
      ∀ f g : ℤ → ℂ, (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let M := ⌈Real.exp (103 * L)⌉₊
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      uniformAverage (fun x : Fin N =>
        let u := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + (a + l * x.val : ℕ)) f
        let v := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + (a + l * x.val : ℕ)) g
        ‖inner ℂ u (primeBlockCompression P M Q actualPaddingCoefficient
          (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
          L K W (fun _ => actualPaddingDegreeCut Qp L) h gate keep
          (a + l * x.val : ℕ) v)‖) ≤
        4 * ((3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ))) := by
  obtain ⟨A, hA, ht⟩ := hprime.eventually_actual_affine_testing_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh hl E hE hEl W hW
  filter_upwards [ht h l hh hl E hE hEl W hW] with L htest
  intro hL η hη hηone eligible he
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Qp := paddingPrimeSupply E L
  let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
  let data := canonicalTraceFamily h E W L eligible hL hW hE
  let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
    (fun d q => (d, q) ∈ data.pairs) z
  let M := ⌈Real.exp (103 * L)⌉₊
  let K := Real.exp (4 * J)
  let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
  intro gate hgate f g hf hg a N hN
  let site (x : Fin N) (i : Fin M) := (i.val : ℤ) + (a + l * x.val : ℕ)
  let T (x : Fin N) := primeBlockCompression P M Q actualPaddingCoefficient
    (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
    L K W (fun _ => actualPaddingDegreeCut Qp L) h gate keep (a + l * x.val : ℕ)
  apply uniformAverage_padding_bilinear Qp L site T _ ?_ f g hf hg
  intro F hF
  exact htest hL η hη hηone eligible he gate hgate F hF a N hN

end TwoPointCorrelations

end OAI
