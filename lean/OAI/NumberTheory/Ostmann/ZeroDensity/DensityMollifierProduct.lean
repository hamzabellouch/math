import Mathlib.NumberTheory.LSeries.Convolution
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorCoefficients
import OAI.NumberTheory.Ostmann.Characters.CharacterRightHalfPlane

namespace OAI

/-! # The actual finite mollifier times the character L-function -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def densityMollifierCoefficient {q : ℕ} (X : ℕ)
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  χ (n : ZMod q) * densityMobiusCutoff X n

noncomputable def densityMollifier {q : ℕ} (X : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, χ (n : ZMod q) * (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s

 theorem density_detector_convolution {q : ℕ} (X : ℕ) (χ : DirichletCharacter ℂ q) :
    LSeries.convolution (fun n : ℕ => χ (n : ZMod q)) (densityMollifierCoefficient X χ) =
      fun n : ℕ => χ (n : ZMod q) * densityDetectorCoefficient X n := by
  funext n
  rw [LSeries.convolution_def]
  change (∑ p ∈ n.divisorsAntidiagonal,
    χ (p.1 : ZMod q) * (χ (p.2 : ZMod q) * densityMobiusCutoff X p.2)) = _
  calc
    _ = χ (n : ZMod q) * ∑ p ∈ n.divisorsAntidiagonal, densityMobiusCutoff X p.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hm := (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [← mul_assoc, ← map_mul, ← Nat.cast_mul, hm]
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ b => densityMobiusCutoff X b)]
      rfl

 theorem densityMollifier_eq_LSeries {q : ℕ} (X : ℕ) (χ : DirichletCharacter ℂ q) (s : ℂ) :
    densityMollifier X χ s = LSeries (densityMollifierCoefficient X χ) s := by
  have hout (n : ℕ) (hn : n ∉ Finset.Icc 1 X) :
      LSeries.term (densityMollifierCoefficient X χ) s n = 0 := by
    by_cases hn0 : n = 0
    · subst n; simp
    · have hnX : ¬n ≤ X := by simp only [Finset.mem_Icc] at hn; omega
      rw [LSeries.term_of_ne_zero hn0]
      simp only [densityMollifierCoefficient, densityMobiusCutoff, ite_eq_right hnX, mul_zero, zero_div]
  rw [LSeries, tsum_eq_sum hout]
  apply Finset.sum_congr rfl
  intro n hn
  have hnn := Finset.mem_Icc.mp hn
  rw [LSeries.term_of_ne_zero (by omega : n ≠ 0)]
  simp only [densityMollifierCoefficient, densityMobiusCutoff, ite_eq_left hnn.2]

 theorem densityMollifierCoefficient_norm {q : ℕ} [NeZero q] (X n : ℕ)
    (χ : DirichletCharacter ℂ q) : ‖densityMollifierCoefficient X χ n‖ ≤ 1 := by
  rw [densityMollifierCoefficient, norm_mul]
  exact (mul_le_mul (χ.norm_le_one _) (densityMobiusCutoff_norm X n)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

 theorem density_mollifier_L_product {q : ℕ} [NeZero q] (X : ℕ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ (n : ZMod q) * densityDetectorCoefficient X n) s =
      DirichletCharacter.LFunction χ s * densityMollifier X χ s := by
  rw [← density_detector_convolution X χ,
    LSeries_convolution' (χ.LSeriesSummable_of_one_lt_re hs)
      (LSeriesSummable_of_bounded_of_one_lt_re
        (fun n _ => densityMollifierCoefficient_norm X n χ) hs),
    DirichletCharacter.LFunction_eq_LSeries χ hs, densityMollifier_eq_LSeries]

end Ostmann

end OAI
