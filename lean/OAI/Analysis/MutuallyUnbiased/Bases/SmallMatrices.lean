import OAI.Analysis.MutuallyUnbiased.Tao.Tao
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! Explicit mutually unbiased bases from two- and three-dimensional unitary matrices. -/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace MUB6.ThreeSmall

abbrev Sq (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def H2 : Sq 2 := !![1, 1; 1, -1]
def G2 : Sq 2 := !![1, 1; Complex.I, -Complex.I]
def H3 : Sq 3 := !![1, 1, 1; 1, omega, omega^2; 1, omega^2, omega]
def G3 : Sq 3 := fun i j => (![1, omega, omega] : Fin 3 → ℂ) i * H3 i j

def normalize {n : ℕ} (H : Sq n) : Sq n :=
  fun i j => (Real.sqrt (n : ℝ) : ℂ)⁻¹ * H i j

def A : Fin 3 → Sq 2 := ![1, normalize H2, normalize G2]
def B : Fin 3 → Sq 3 := ![1, normalize H3, normalize G3]

lemma normalizer_normSq (n : ℕ) :
    Complex.normSq ((Real.sqrt (n : ℝ) : ℂ)⁻¹) = (1 : ℝ) / n := by
  rw [Complex.normSq_inv, Complex.normSq_ofReal, ← sq,
    Real.sq_sqrt (Nat.cast_nonneg n)]
  simp [one_div]

lemma normalized_cross_entry {n : ℕ} (H G : Sq n) (i j : Fin n) :
    ((normalize H).conjTranspose * normalize G) i j =
      (conj ((Real.sqrt (n : ℝ) : ℂ)⁻¹) * (Real.sqrt (n : ℝ) : ℂ)⁻¹) *
        (H.conjTranspose * G) i j := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, normalize]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [← starRingEnd_apply, map_mul]
  ring

lemma normalized_gram {n : ℕ} (hn : 0 < n) (H : Sq n)
    (hH : H.conjTranspose * H = (n : ℂ) • (1 : Sq n)) :
    (normalize H).conjTranspose * normalize H = 1 := by
  ext i j
  rw [normalized_cross_entry, hH, ← Complex.normSq_eq_conj_mul_self,
    normalizer_normSq]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  by_cases hij : i = j
  · subst j
    simp [Matrix.smul_apply, smul_eq_mul, hnC]
  · simp [Matrix.smul_apply, smul_eq_mul, hij]

lemma normalized_entry_normSq {n : ℕ} (H : Sq n) (i j : Fin n) :
    Complex.normSq (normalize H i j) = ((1 : ℝ) / n) * Complex.normSq (H i j) := by
  simp only [normalize, Complex.normSq_mul, normalizer_normSq]

lemma normalized_cross_normSq {n : ℕ} (H G : Sq n) (i j : Fin n) :
    Complex.normSq (((normalize H).conjTranspose * normalize G) i j) =
      (((1 : ℝ) / n) * ((1 : ℝ) / n)) *
        Complex.normSq ((H.conjTranspose * G) i j) := by
  simp only [normalized_cross_entry, Complex.normSq_mul, Complex.normSq_conj,
    normalizer_normSq]

lemma cross_normSq_swap {n : ℕ} (H G : Sq n) (i j : Fin n) :
    Complex.normSq ((H.conjTranspose * G) i j) =
      Complex.normSq ((G.conjTranspose * H) j i) := by
  have he : conj ((H.conjTranspose * G) i j) =
      (G.conjTranspose * H) j i := by
    change ((H.conjTranspose * G).conjTranspose) j i = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [← he, Complex.normSq_conj]

lemma H2_gram : H2.conjTranspose * H2 = (2 : ℂ) • (1 : Sq 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [H2, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ]

lemma G2_gram : G2.conjTranspose * G2 = (2 : ℂ) • (1 : Sq 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [G2, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Complex.I_sq]

lemma H3_gram : H3.conjTranspose * H3 = (3 : ℂ) • (1 : Sq 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [H3, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ, omega_conj] <;>
    ring_nf <;> norm_num [omega_cube, omega_four, omega_five, omega_six] <;>
    linear_combination omega_sum

lemma G3_gram : G3.conjTranspose * G3 = (3 : ℂ) • (1 : Sq 3) := by
  rw [← H3_gram]
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hphase : conj ((![1, omega, omega] : Fin 3 → ℂ) k) *
      ((![1, omega, omega] : Fin 3 → ℂ) k) = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self]
    fin_cases k <;> simp [omega_normSq]
  change conj (((![1, omega, omega] : Fin 3 → ℂ) k) * H3 k i) *
    (((![1, omega, omega] : Fin 3 → ℂ) k) * H3 k j) = _
  rw [map_mul]
  calc
    _ = (conj ((![1, omega, omega] : Fin 3 → ℂ) k) *
        ((![1, omega, omega] : Fin 3 → ℂ) k)) * (conj (H3 k i) * H3 k j) := by ring
    _ = _ := by rw [hphase, one_mul]; simp only [starRingEnd_apply]

lemma H2_unit (i j : Fin 2) : Complex.normSq (H2 i j) = 1 := by
  fin_cases i <;> fin_cases j <;> norm_num [H2]
lemma G2_unit (i j : Fin 2) : Complex.normSq (G2 i j) = 1 := by
  fin_cases i <;> fin_cases j <;> norm_num [G2]
lemma H3_unit (i j : Fin 3) : Complex.normSq (H3 i j) = 1 := by
  fin_cases i <;> fin_cases j <;> simp [H3, map_pow, omega_normSq]
lemma G3_unit (i j : Fin 3) : Complex.normSq (G3 i j) = 1 := by
  simp only [G3, Complex.normSq_mul, H3_unit, mul_one]
  fin_cases i <;> simp [omega_normSq]

lemma H2_G2_cross (i j : Fin 2) :
    Complex.normSq ((H2.conjTranspose * G2) i j) = 2 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [H2, G2, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.normSq_apply]

private lemma omega_sq_reduce : omega^2 = -1-omega := by
  linear_combination omega_sum
private lemma omega_seven : omega^7 = omega := by
  calc
    omega^7 = omega^6 * omega := by ring
    _ = omega := by rw [omega_six]; ring
private lemma omega_eight : omega^8 = omega^2 := by
  calc
    omega^8 = omega^6 * omega^2 := by ring
    _ = omega^2 := by rw [omega_six]; ring

private lemma omega_pow_mod3 (n : ℕ) : omega ^ n = omega ^ (n % 3) := by
  exact pow_eq_pow_mod n omega_cube

lemma H3_G3_cross (i j : Fin 3) :
    Complex.normSq ((H3.conjTranspose * G3) i j) = 3 := by
  apply Complex.ofReal_injective
  change (Complex.normSq ((H3.conjTranspose * G3) i j) : ℂ) = 3
  rw [← Complex.mul_conj]
  fin_cases i <;> fin_cases j <;>
    simp [H3, G3, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, omega_conj] <;>
    ring_nf <;> norm_num [omega_cube, omega_four, omega_five, omega_six,
      omega_seven, omega_eight,
      omega_pow_mod3 9, omega_pow_mod3 10, omega_pow_mod3 11, omega_pow_mod3 12, omega_pow_mod3 13, omega_pow_mod3 14, omega_pow_mod3 15, omega_pow_mod3 16, omega_pow_mod3 17, omega_pow_mod3 18, omega_pow_mod3 19, omega_pow_mod3 20, omega_pow_mod3 21] <;>
    simp only [omega_sq_reduce] <;> ring

theorem A_gram (r : Fin 3) : (A r).conjTranspose * A r = 1 := by
  fin_cases r
  · simp [A]
  · simpa [A] using normalized_gram (by decide : 0 < 2) H2 H2_gram
  · simpa [A] using normalized_gram (by decide : 0 < 2) G2 G2_gram
theorem B_gram (r : Fin 3) : (B r).conjTranspose * B r = 1 := by
  fin_cases r
  · simp [B]
  · simpa [B] using normalized_gram (by decide : 0 < 3) H3 H3_gram
  · simpa [B] using normalized_gram (by decide : 0 < 3) G3 G3_gram

lemma A01 (i j : Fin 2) : Complex.normSq (((A 0).conjTranspose * A 1) i j) = (1:ℝ)/2 := by
  simp [A, normalized_entry_normSq, H2_unit]
lemma A02 (i j : Fin 2) : Complex.normSq (((A 0).conjTranspose * A 2) i j) = (1:ℝ)/2 := by
  simp [A, normalized_entry_normSq, G2_unit]
lemma A12 (i j : Fin 2) : Complex.normSq (((A 1).conjTranspose * A 2) i j) = (1:ℝ)/2 := by
  change Complex.normSq (((normalize H2).conjTranspose * normalize G2) i j) = (1:ℝ)/2
  rw [normalized_cross_normSq, H2_G2_cross]
  norm_num
lemma B01 (i j : Fin 3) : Complex.normSq (((B 0).conjTranspose * B 1) i j) = (1:ℝ)/3 := by
  simp [B, normalized_entry_normSq, H3_unit]
lemma B02 (i j : Fin 3) : Complex.normSq (((B 0).conjTranspose * B 2) i j) = (1:ℝ)/3 := by
  simp [B, normalized_entry_normSq, G3_unit]
lemma B12 (i j : Fin 3) : Complex.normSq (((B 1).conjTranspose * B 2) i j) = (1:ℝ)/3 := by
  change Complex.normSq (((normalize H3).conjTranspose * normalize G3) i j) = (1:ℝ)/3
  rw [normalized_cross_normSq, H3_G3_cross]
  norm_num

theorem A_cross_normSq (r s : Fin 3) (hrs : r ≠ s) (i j : Fin 2) :
    Complex.normSq (((A r).conjTranspose * A s) i j) = (1:ℝ)/2 := by
  fin_cases r <;> fin_cases s
  all_goals first
    | exact False.elim (hrs rfl)
    | exact A01 i j
    | exact A02 i j
    | exact A12 i j
    | exact (cross_normSq_swap _ _ _ _).trans (A01 j i)
    | exact (cross_normSq_swap _ _ _ _).trans (A02 j i)
    | exact (cross_normSq_swap _ _ _ _).trans (A12 j i)
theorem B_cross_normSq (r s : Fin 3) (hrs : r ≠ s) (i j : Fin 3) :
    Complex.normSq (((B r).conjTranspose * B s) i j) = (1:ℝ)/3 := by
  fin_cases r <;> fin_cases s
  all_goals first
    | exact False.elim (hrs rfl)
    | exact B01 i j
    | exact B02 i j
    | exact B12 i j
    | exact (cross_normSq_swap _ _ _ _).trans (B01 j i)
    | exact (cross_normSq_swap _ _ _ _).trans (B02 j i)
    | exact (cross_normSq_swap _ _ _ _).trans (B12 j i)

end MUB6.ThreeSmall

end

end OAI
