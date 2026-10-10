import OAI.NumberTheory.TwoPoint.Bounds.ActualAffineIntervalMatrix
import OAI.NumberTheory.TwoPoint.Bounds.MatrixSpectralTail

namespace OAI

/-! Exceptional origins along a fixed progression for the actual finite block. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_actual_affine_spectral_tail_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (E : Finset ℕ)
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
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
        (fun d => centeredTuple d.primeFactors) L (Real.exp (4 * J))
        (fun _ => actualPaddingDegreeCut Qp L) h
        (fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z)
      ∀ gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop,
      let matrix := fun c : ℤ => shiftMatrix
        (primeBlockEmbedding (P := P) ⌈Real.exp (103 * L)⌉₊)
        (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
        (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h gate
          (fun t n => weight t (n + c)))
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => if
        Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J)) <
          realMatrixSpectralRadius (matrix (a + l * x.val : ℕ)) then (1 : ℝ) else 0) ≤
        Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨A, hA, htrace⟩ := hprime.eventually_actual_affine_interval_matrix_uniform hBr
  refine ⟨A, hA, ?_⟩
  intro h l hh E hE hEl W hW
  have htrace := htrace h l hh E hE hEl W hW
  filter_upwards [htrace] with L htrace
  intro hL η hη hηone eligible he
  dsimp only
  intro gate a N hN
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := (Real.exp_pos _).trans_le hN
    exact_mod_cast this
  let : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  have hk : 0 < ⌊L⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ L)).mpr (by simpa using hL)
  have hsqrt : 1 ≤ Real.sqrt W := by simpa using Real.sqrt_le_sqrt hW
  have hbase : 1 ≤ Real.exp (4 * (primeSupplyCount W L : ℝ)) *
      (2 * Real.exp 150 * Real.sqrt W) ^ primeSupplyCount W L := by
    have hinner : 1 ≤ 2 * Real.exp 150 * Real.sqrt W := by
      have hx : 1 ≤ 2 * Real.exp 150 := by linarith [Real.one_le_exp (show (0 : ℝ) ≤ 150 by norm_num)]
      simpa only [one_mul] using mul_le_mul hx hsqrt zero_le_one (by positivity)
    simpa only [one_mul] using mul_le_mul
      (Real.one_le_exp (show 0 ≤ 4 * (primeSupplyCount W L : ℝ) by positivity))
      (one_le_pow₀ hinner) zero_le_one (Real.exp_pos _).le
  have hm := htrace hL η hη hηone eligible he gate a N hN
  rw [← FiniteLaw.uniform_average] at hm
  have ht := (FiniteLaw.uniform (Fin N)).matrix_spectral_tail_add_one _ ⌊L⌋₊ hk _ hbase hm
  simpa only [FiniteLaw.probability, FiniteLaw.uniform_average] using ht

theorem ModFiveThetaInput.eventually_actual_affine_spectral_tail
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input)
    (h l : ℕ) (hh : 0 < h) (E : Finset ℕ)
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
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
        (fun d => centeredTuple d.primeFactors) L (Real.exp (4 * J))
        (fun _ => actualPaddingDegreeCut Qp L) h
        (fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z)
      ∀ gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop,
      let matrix := fun c : ℤ => shiftMatrix
        (primeBlockEmbedding (P := P) ⌈Real.exp (103 * L)⌉₊)
        (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
        (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h gate
          (fun t n => weight t (n + c)))
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => if
        Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J)) <
          realMatrixSpectralRadius (matrix (a + l * x.val : ℕ)) then (1 : ℝ) else 0) ≤
        Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  obtain ⟨A, hA, hbound⟩ := hprime.eventually_actual_affine_spectral_tail_uniform hBr
  exact ⟨A, hA, hbound h l hh E hE hEl W hW⟩

end TwoPointCorrelations

end OAI
