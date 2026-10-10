import OAI.NumberTheory.TwoPoint.Bounds.ComplexBlockTesting

namespace OAI

/-! The canonical spectral estimate applied to two arbitrary complex sequences.
The short-range hypothesis only selects the ten color tests. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_canonical_complex_blocks
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
      uniformAverage (fun t : Fin N =>
        ‖retainedComplexBlock P M Q Qp actualPaddingCoefficient active L K W
          (fun _ => actualPaddingDegreeCut Qp L) h (fun _ _ _ => True) keep F G t.val‖) ≤
        40 * ((3 * R) * (2 * M * paddingTiltNormalizer Qp) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ))) := by
  obtain ⟨A, hA, hb⟩ := hprime.eventually_actual_affine_bilinear_testing hBr
  refine ⟨A, hA, ?_⟩
  intro h hh E hE W hW
  filter_upwards [hb h 1 hh (by norm_num) E hE
    (fun p hp hdiv => False.elim (hp.not_dvd_one hdiv)) W hW] with L hb
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
  have hp := centeredPrimeBands_prime E (L ^ (199 / 200 : ℝ)) W J
  have hd := centeredPrimeBands_disjoint E (L ^ (199 / 200 : ℝ)) W J
    (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hshift : ∀ d : (j : Fin J) → P j, ∀ q ∈ Q, active (∏ j, (d j).val) q →
      D ≤ (h * q * ∏ j, (d j).val : ℕ) ∧ (h * q * ∏ j, (d j).val : ℕ) < 2 * D := by
    intro d q _hq hact
    exact hs _ _ (canonicalTraceFamily_pair_eligible h E W L eligible hL hW hE _ _ hact)
  have ht (c : ForwardColorCode) : uniformAverage (fun t : Fin N =>
      ‖ambientComplexBlockTest P M Q Qp actualPaddingCoefficient active L K W
        (fun _ => actualPaddingDegreeCut Qp L) h (fun _ _ _ => True) keep
        (fun n => if sourceColor D c n then F n else 0)
        (fun n => if targetColor D c n then G n else 0) t.val‖) ≤
      4 * ((3 * R) * (2 * M * paddingTiltNormalizer Qp) +
        ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
          Real.exp (-(2 * ⌊L⌋₊ : ℕ))) := by
    have hf (n : ℤ) : ‖star (if sourceColor D c n then F n else 0)‖ ≤ 1 := by
      rw [norm_star]
      exact sourceColorFunction_norm_le D id c F hF n
    have hg (n : ℤ) : ‖if targetColor D c n then G n else 0‖ ≤ 1 :=
      targetColorFunction_norm_le D id c G hG n
    have htest := hb hL η hη hηone eligible he (fun _ _ _ => True)
      (fun _ _ _ => Iff.rfl) (fun n => star (if sourceColor D c n then F n else 0))
      (fun n => if targetColor D c n then G n else 0) hf hg 2 N hN
    simpa only [ambientComplexBlockTest, Nat.cast_one, one_mul, Nat.one_mul, Nat.add_comm] using htest
  have hr := retainedComplexBlock_average_le P hp hd M N Q Qp actualPaddingCoefficient
    active L K W (fun _ => actualPaddingDegreeCut Qp L) h (fun _ _ _ => True)
    (fun _ _ _ => Iff.rfl) keep D hD hshift F G _ ht
  linarith

end TwoPointCorrelations

end OAI
