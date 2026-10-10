import OAI.NumberTheory.Ostmann.ZeroDensity.DensityMollifierProduct
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorKernel

namespace OAI

/-! # The true truncated Mobius series in the zero detector -/

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

noncomputable def densityDetectorCharacterCoefficient (χ : PrimitiveComplexCharacter)
    (X n : ℕ) : ℂ := χ.character (n : ZMod χ.modulus) * densityDetectorCoefficient X n

noncomputable def densityDetectorMean (χ : PrimitiveComplexCharacter) (X : ℕ)
    (s : ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, LSeries.term (densityDetectorCharacterCoefficient χ X) s n *
    densityDetectorWeight (n / Y)

 theorem densityDetectorCharacterCoefficient_norm (χ : PrimitiveComplexCharacter) (X n : ℕ) :
    ‖densityDetectorCharacterCoefficient χ X n‖ ≤ n.divisors.card := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  rw [densityDetectorCharacterCoefficient, norm_mul]
  apply (mul_le_mul (χ.character.norm_le_one _) (densityDetectorCoefficient_norm X n)
    (norm_nonneg _) zero_le_one).trans_eq
  ring

 theorem densityDetectorMean_split (χ : PrimitiveComplexCharacter) (X : ℕ) (hX : 1 ≤ X)
    (s : ℂ) (Y : ℝ) (hY : 1 ≤ Y) :
    densityDetectorMean χ X s Y = densityDetectorWeight (1 / Y) +
      ∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
        LSeries.term (densityDetectorCharacterCoefficient χ X) s n * densityDetectorWeight (n / Y) := by
  let U := Finset.Icc 1 ⌊Y⌋₊
  have h1 : 1 ∈ U := Finset.mem_Icc.mpr ⟨le_rfl, (Nat.le_floor_iff (by linarith : 0 ≤ Y)).mpr (by simpa using hY)⟩
  have hf : ∑ n ∈ U, LSeries.term (densityDetectorCharacterCoefficient χ X) s n * densityDetectorWeight (n / Y) =
      ∑ n ∈ U, ((if n = 1 then densityDetectorWeight (1 / Y) else 0) +
        (if X < n then LSeries.term (densityDetectorCharacterCoefficient χ X) s n *
          densityDetectorWeight (n / Y) else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hn1 : n = 1
    · subst n
      simp [densityDetectorCharacterCoefficient, densityDetectorCoefficient_one hX,
        LSeries.term_of_ne_zero, show ¬ X < 1 by omega]
    · by_cases hnX : X < n
      · simp [hn1, hnX]
      · have hn2 : 2 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
        have hz := densityDetectorCoefficient_small hn2 (by omega : n ≤ X)
        simp [hn1, hnX, LSeries.term_of_ne_zero (show n ≠ 0 by omega),
          densityDetectorCharacterCoefficient, hz]
  unfold densityDetectorMean
  rw [hf, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', h1, ↓reduceIte, Finset.sum_filter]
  rfl

end Ostmann

namespace Ostmann

open Complex MeasureTheory Set
open scoped BigOperators Classical

 theorem densityDetectorCharacterCoefficient_summable (χ : PrimitiveComplexCharacter)
    (X : ℕ) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (densityDetectorCharacterCoefficient χ X) s := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have h := (χ.character.LSeriesSummable_of_one_lt_re hs).convolution
    (LSeriesSummable_of_bounded_of_one_lt_re
      (fun n _ => densityMollifierCoefficient_norm X n χ.character) hs)
  rw [density_detector_convolution] at h
  exact h

 theorem densityDetectorMean_tsum (χ : PrimitiveComplexCharacter) (X : ℕ) (s : ℂ)
    (Y : ℝ) (hY : 0 < Y) :
    densityDetectorMean χ X s Y = ∑' n : ℕ,
      LSeries.term (densityDetectorCharacterCoefficient χ X) s n * densityDetectorWeight (n / Y) := by
  symm
  apply tsum_eq_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0]
  · have hnY : Y < n := by
      have hnN : ⌊Y⌋₊ < n := by
        by_contra h
        exact hn (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      exact (Nat.floor_lt (by positivity : 0 ≤ Y)).mp hnN
    rw [densityDetectorWeight_zero _ ((le_div_iff₀ hY).mpr (by simpa using hnY.le)), mul_zero]

end Ostmann

end OAI
