import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basis
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring

namespace OAI

/-! The only tracial linear functional on a full finite matrix algebra is
its value at the identity times the normalized matrix trace. -/

noncomputable section
namespace KadisonSimilarity

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Matrix units determine a tracial functional, without positivity. -/
theorem matrix_tracial_functional (F : Matrix ι ι ℂ →ₗ[ℂ] ℂ)
    (htr : ∀ a b, F (a * b) = F (b * a)) (a : Matrix ι ι ℂ) :
    F a = (Fintype.card ι : ℂ)⁻¹ * F 1 * Matrix.trace a := by
  classical
  let k : ι := Classical.arbitrary ι
  have hdiag (i : ι) : F (Matrix.single i i 1) = F (Matrix.single k k 1) := by
    simpa only [Matrix.single_mul_single_same, one_mul] using
      htr (Matrix.single i k 1) (Matrix.single k i 1)
  have hoff (i j : ι) (hij : i ≠ j) : F (Matrix.single i j 1) = 0 := by
    have h := htr (Matrix.single i i 1) (Matrix.single i j 1)
    have hz : Matrix.single i j (1 : ℂ) * Matrix.single i i 1 = 0 := by
      apply Matrix.single_mul_single_of_ne
      exact hij.symm
    simpa only [Matrix.single_mul_single_same, hz, one_mul, map_zero] using h
  have hunit : F 1 = (Fintype.card ι : ℂ) * F (Matrix.single k k 1) := by
    rw [← Matrix.sum_single_one, map_sum]
    simp only [hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hd : F (Matrix.single k k 1) = (Fintype.card ι : ℂ)⁻¹ * F 1 := by
    rw [hunit, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  have hentry (i j : ι) (z : ℂ) :
      F (Matrix.single i j z) =
        if i = j then z * ((Fintype.card ι : ℂ)⁻¹ * F 1) else 0 := by
    have hs : Matrix.single i j z = z • Matrix.single i j (1 : ℂ) := by
      rw [Matrix.smul_single]
      simp only [smul_eq_mul, mul_one]
    rw [hs, map_smul, smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, hdiag, hd]
    · simp only [hij, ite_false, hoff i j hij, mul_zero]
  calc
    F a = ∑ i, ∑ j, F (Matrix.single i j (Matrix.of.symm a i j)) := by
      simpa only [map_sum, Matrix.of_symm_apply] using congrArg F (Matrix.matrix_eq_sum_single a)
    _ = ∑ i, Matrix.of.symm a i i * ((Fintype.card ι : ℂ)⁻¹ * F 1) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [hentry]
      simp
    _ = (Fintype.card ι : ℂ)⁻¹ * F 1 * Matrix.trace a := by
      rw [← Finset.sum_mul]
      change Matrix.trace a * ((Fintype.card ι : ℂ)⁻¹ * F 1) = _
      ring

end KadisonSimilarity

end

end OAI
