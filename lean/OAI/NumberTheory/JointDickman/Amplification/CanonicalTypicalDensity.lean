import OAI.NumberTheory.JointDickman.Analysis.CanonicalMellinBands
import OAI.NumberTheory.JointDickman.Counting.TypicalShortEnergy
import OAI.NumberTheory.TwoPointCorrelations.MRTTypicalDensity

namespace OAI

/-! # Counting and restoring the canonical typical set -/
namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical

lemma canonical_typical_iff (P Q η : ℝ) (J n : ℕ) :
    mrtTypical (range J) (canonicalMellinBands P Q η).primes n ↔
      mrtTypical univ
        (fun j : {j : ℕ // j ∈ (Icc 1 J : Finset ℕ)} =>
          mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) n := by
  constructor
  · intro h j _
    have hj : j.val-1 ∈ range J := mem_range.mpr (by have := mem_Icc.mp j.property; omega)
    have he : j.val-1+1 = j.val := by have := mem_Icc.mp j.property; omega
    simpa only [canonicalMellinBands, he] using h (j.val-1) hj
  · intro h j hj
    have hj' : j+1 ∈ Icc 1 J := mem_Icc.mpr ⟨by omega, by have := mem_range.mp hj; omega⟩
    exact h ⟨j+1, hj'⟩ (mem_univ _)

lemma uniformFiniteLaw_nat_count (N : ℕ) [NeZero N] (E : ℕ → Prop) :
    (uniformFiniteLaw (Fin N)).probability (fun j => E j.val) =
      (((range N).filter E).card : ℝ) / N := by
  unfold TwoPointCorrelations.FiniteLaw.probability TwoPointCorrelations.FiniteLaw.average
    uniformFiniteLaw
  simp only [Fintype.card_fin]
  rw [← mul_sum, Fin.sum_univ_eq_sum_range (fun n : ℕ => if E n then (1 : ℝ) else 0) N]
  rw [sum_boole]
  ring

theorem canonical_typical_count : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ (P Q η : ℝ) (J N : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      (∀ j ∈ range J, mrtBandUpper Q (j+1) ≤ Real.exp (L^(99/100 : ℝ))) →
      0 < N → (1/2 : ℝ)*Real.exp (L^(199/200 : ℝ)) ≤ N →
      (((range N).filter fun n =>
          ¬mrtTypical (range J) (canonicalMellinBands P Q η).primes n).card : ℝ) / N ≤
        C*Real.log P/Real.log Q := by
  obtain ⟨C, hC, hbound⟩ := mrt_typical_density
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with L hL
  intro P Q η J N hP hPQ hQ hmax hN hsize
  let : NeZero N := ⟨hN.ne'⟩
  have hmax' : ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (L^(99/100 : ℝ)) := by
    intro j hj
    have hj' : j-1 ∈ range J := mem_range.mpr (by have := mem_Icc.mp hj; omega)
    simpa only [show j-1+1 = j by have := mem_Icc.mp hj; omega] using hmax (j-1) hj'
  have hh := hL P Q J hP hPQ hQ hmax' 0 N hsize
  simp only [Nat.zero_add, ← canonical_typical_iff P Q η J] at hh
  rw [uniformFiniteLaw_nat_count N (fun n =>
    ¬mrtTypical (range J) (canonicalMellinBands P Q η).primes n)] at hh
  convert hh using 2
  apply congrArg (fun k : ℕ => (k : ℝ))
  apply congrArg Finset.card
  ext n
  simp only [mem_filter]

lemma restrictArithmetic_eq_typical (P Q η : ℝ) (J : ℕ) (f : ArithmeticFunction ℂ) :
    (restrictArithmetic (mrtTypical (range J) (canonicalMellinBands P Q η).primes) f : ℕ → ℂ) =
      mrtTypicalCoefficient (range J) (canonicalMellinBands P Q η).primes f := by
  funext n
  simp only [restrictArithmetic, ArithmeticFunction.coe_mk, mrtTypicalCoefficient]

/-- The exact prefix removed by the short-energy transfer has small ordinary
density. Its scale is three times the original short-average location. -/
theorem canonical_typical_prefix_count : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ L : ℝ in atTop, ∀ (P Q η X : ℝ) (J : ℕ),
      2 ≤ P → P ≤ Q → 1 ≤ Real.log Q → 1 ≤ X →
      (∀ j ∈ range J, mrtBandUpper Q (j+1) ≤ Real.exp (L^(99/100 : ℝ))) →
      (1/2 : ℝ)*Real.exp (L^(199/200 : ℝ)) ≤ 3*X →
      (((range (⌊3*X⌋₊+1)).filter fun n =>
          ¬mrtTypical (range J) (canonicalMellinBands P Q η).primes n).card : ℝ) / X ≤
        C*Real.log P/Real.log Q := by
  obtain ⟨C, hC, hbound⟩ := canonical_typical_count
  refine ⟨4*C, by positivity, ?_⟩
  filter_upwards [hbound] with L hL
  intro P Q η X J hP hPQ hQ hX hmax hsize
  have hX0 : 0 < X := by linarith
  have hfloor := Nat.lt_floor_add_one (3*X)
  have hsize' : (1/2 : ℝ)*Real.exp (L^(199/200 : ℝ)) ≤ (⌊3*X⌋₊+1 : ℕ) := by
    push_cast
    linarith
  have hh := hL P Q η J (⌊3*X⌋₊+1) hP hPQ hQ hmax (by omega) hsize'
  have hmaxN : (⌊3*X⌋₊+1 : ℕ) ≤ 4*X := by
    have hf := Nat.floor_le (by linarith : 0 ≤ 3*X)
    push_cast
    linarith
  have hR : 0 ≤ C*Real.log P/Real.log Q := by
    exact div_nonneg (mul_nonneg hC.le (Real.log_nonneg (by linarith))) (by linarith)
  have hn0 : (0 : ℝ) < (⌊3*X⌋₊+1 : ℕ) := by positivity
  apply (div_le_iff₀ hX0).mpr
  have hh' := (div_le_iff₀ hn0).mp hh
  calc
    _ ≤ (C*Real.log P/Real.log Q)*(⌊3*X⌋₊+1 : ℕ) := hh'
    _ ≤ (C*Real.log P/Real.log Q)*(4*X) := mul_le_mul_of_nonneg_left hmaxN hR
    _ = _ := by ring

end JointDickman

end OAI
