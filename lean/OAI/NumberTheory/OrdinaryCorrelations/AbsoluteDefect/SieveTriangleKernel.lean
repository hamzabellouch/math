import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TriangleMain
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Reciprocal

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace OrdinarySelbergWeights
open Finset OrdinaryLogIntegral

noncomputable def sieveTriangleKernel (t : ℝ) (B P z : ℕ) (hP : Squarefree P) : ℂ :=
  ∑ n ∈ range (6*B+1), (sieveWeight P z hP n : ℂ)*tentPhase t B (2*B) n

lemma sieveTriangleKernel_expansion (t : ℝ) (B P z : ℕ) (hP : Squarefree P) :
    sieveTriangleKernel t B P z hP =
      ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        (actualWeights P z hP d * actualWeights P z hP e : ℝ) •
          divisorTriangle t B (Nat.lcm d e) := by
  unfold sieveTriangleKernel
  simp_rw [sieveWeight_expansion, Complex.ofReal_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  simp only [divisorTriangle, smul_sum, Complex.real_smul]
  apply sum_congr rfl
  intro n hn
  split_ifs <;> simp_all

lemma sieveTriangleKernel_main (t : ℝ) (B P z : ℕ) (hP : Squarefree P) (hz : 1 ≤ z) :
    (∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
      (actualWeights P z hP d * actualWeights P z hP e : ℝ) •
        (((Nat.lcm d e : ℝ)⁻¹ : ℝ) • triangleMain t B)) =
      ((actualMass P z hP)⁻¹ : ℝ) • triangleMain t B := by
  simp_rw [smul_smul, ← sum_smul, ← div_eq_mul_inv]
  rw [actualWeights_diagonal hP hz]

theorem sieveTriangleKernel_error (t : ℝ) (u P z : ℕ) (hP : Squarefree P)
    (hu : 1 ≤ u) (hz : 1 ≤ z) (hzB : z^2 ≤ u^8) (ht : |t| ≤ (u : ℝ)^10) :
    ‖sieveTriangleKernel t (u^8) P z hP -
      ((actualMass P z hP)⁻¹ : ℝ) • triangleMain t (u^8)‖ ≤
        (z : ℝ)^4 * (1600*(u : ℝ)^7) := by
  let w := actualWeights P z hP
  let E : ℝ := 1600*(u : ℝ)^7
  have hE : 0 ≤ E := by dsimp [E]; positivity
  rw [sieveTriangleKernel_expansion, ← sieveTriangleKernel_main t (u^8) P z hP hz,
    ← sum_sub_distrib]
  have heach (d : ℕ) (hd : d ∈ P.divisors) (e : ℕ) (he : e ∈ P.divisors) :
      ‖(w d*w e : ℝ) • divisorTriangle t (u^8) (Nat.lcm d e) -
        (w d*w e : ℝ) • (((Nat.lcm d e : ℝ)⁻¹ : ℝ) • triangleMain t (u^8))‖ ≤
          |w d| *|w e| *E := by
    by_cases hdz : d ≤ z
    · by_cases hez : e ≤ z
      · have hde : 0 < Nat.lcm d e := Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)
        have hB : Nat.lcm d e ≤ u^8 := by
          apply (Nat.lcm_le_mul (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)).trans
          exact (Nat.mul_le_mul hdz hez).trans (by simpa [pow_two] using hzB)
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (divisorTriangle_uniform t u (Nat.lcm d e) hu hde hB ht)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      · have hw : w e = 0 := actualWeights_zero_above hP (lt_of_not_ge hez) (Nat.dvd_of_mem_divisors he)
        simp [hw]
    · have hw : w d = 0 := actualWeights_zero_above hP (lt_of_not_ge hdz) (Nat.dvd_of_mem_divisors hd)
      simp [hw]
  calc
    _ ≤ ∑ d ∈ P.divisors, ∑ e ∈ P.divisors, |w d| *|w e| *E := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro d hd
      rw [← sum_sub_distrib]
      exact (norm_sum_le _ _).trans (sum_le_sum (fun e he => heach d hd e he))
    _ = (∑ d ∈ P.divisors, |w d|)^2*E := by
      rw [pow_two, sum_mul_sum]
      simp only [sum_mul]
    _ ≤ _ := by
      have hl := actualWeights_l1 (P := P) hP hz
      change (∑ d ∈ P.divisors, |w d|) ≤ (z : ℝ)^2 at hl
      have hh := mul_le_mul_of_nonneg_right (sq_le_sq₀ (sum_nonneg (fun _ _ => abs_nonneg _)) (sq_nonneg (z : ℝ)) |>.mpr hl) hE
      simpa [E, ← pow_mul] using hh

end OrdinarySelbergWeights

end

end OAI
