import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeMatrix
import OAI.NumberTheory.TwoPoint.Bounds.PrimeBlockDimension

namespace OAI

/-! The actual finite block has the dimension required by the residue trace bound. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

def primeBlockEmbedding {J : ℕ} {P : Fin J → Finset ℕ} (N : ℕ) :
    (((j : Fin J) → P j) × Fin N) → (((j : Fin J) → P j) × ℤ) :=
  fun x => (x.1, (x.2.val : ℤ))

lemma primeBlockEmbedding_injective {J : ℕ} {P : Fin J → Finset ℕ} (N : ℕ) :
    Function.Injective (primeBlockEmbedding (P := P) N) := by
  intro a b hab
  apply Prod.ext
  · exact congrArg (fun z : ((j : Fin J) → P j) × ℤ => z.1) hab
  · apply Fin.ext
    have he : (a.2.val : ℤ) = (b.2.val : ℤ) := congrArg Prod.snd hab
    exact_mod_cast he

theorem ModFiveThetaInput.eventually_actual_block_trace (hprime : ModFiveThetaInput)
    (h : ℕ) (hh : 0 < h) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let B := ⌊Real.exp L⌋₊
      let hB := canonicalTraceFamily_residue_bound h E W L eligible hL hW hE
      let g := actualPaddingVertex Qp
      let keep := fun n => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) n
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) g (fun d => centeredTuple d.primeFactors)
        L (Real.exp (4 * J)) (fun _ => actualPaddingDegreeCut Qp L) h keep
      let N := ⌈Real.exp (103 * L)⌉₊
      ∀ gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop,
      (data.residueLaw B hB).average (fun r => matrixFrobeniusSq
        (shiftMatrix (primeBlockEmbedding (P := P) N)
          (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
          (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h gate
            (fun t n => weight t (n + data.residueOrigin r))) ^ ⌊L⌋₊)) ≤
        (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) := by
  filter_upwards [hprime.eventually_actual_prime_matrix_trace h hh E hE W hW] with L htrace
  intro hL η hη hηone eligible he
  dsimp only
  intro gate
  exact htrace hL η hη hηone eligible he _ (primeBlockEmbedding _)
    (primeBlockEmbedding_injective _) (actual_prime_block_dimension E W L hW hL) gate

end TwoPointCorrelations

end OAI
