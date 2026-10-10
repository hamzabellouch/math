import OAI.NumberTheory.Ostmann.QuadraticSieveGaussRowsBasic
import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationProduct

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def gaussRowCoefficients (c : ℤ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * gaussRowFactor c n

theorem norm_gaussRowFactor_sq_le (c : ℤ) {n : ℕ} (hn : 0 < n) :
    ‖gaussRowFactor c n‖ ^ 2 ≤ 1 / (n : ℝ) := by
  rw [gaussRowFactor, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  apply div_le_div_of_nonneg_right _ (le_of_lt (Nat.cast_pos.mpr hn))
  rcases jacobiSym.trichotomy c n with h | h | h <;> simp [h]

theorem coefficientEnergy_gaussRowCoefficients_le (S : Finset ℕ) (a : ℕ → ℂ)
    (c : ℤ) {L : ℝ} (hL : 0 < L) (hS : ∀ n ∈ S, L ≤ (n : ℝ)) :
    coefficientEnergy S (gaussRowCoefficients c a) ≤ coefficientEnergy S a / L := by
  calc
    _ ≤ ∑ n ∈ S, ‖a n‖ ^ 2 / L := by
      unfold coefficientEnergy
      apply Finset.sum_le_sum
      intro n hn
      have hnr : (0 : ℝ) < n := hL.trans_le (hS n hn)
      have hnp : 0 < n := by exact_mod_cast hnr
      have hf := (norm_gaussRowFactor_sq_le c hnp).trans
        (one_div_le_one_div_of_le hL (hS n hn))
      rw [gaussRowCoefficients, norm_mul, mul_pow, div_eq_mul_inv]
      simpa only [one_div] using mul_le_mul_of_nonneg_left hf (sq_nonneg ‖a n‖)
    _ = _ := by simp only [coefficientEnergy, Finset.sum_div]

theorem gauss_ratio_product_row {n t : ℕ} (hn : Odd n) (ht : Odd t)
    (hns : Squarefree n) (hts : Squarefree t) (hnt : Nat.Coprime n t) (c v : ℤ) :
    jacobiGaussRatio (n * t) * (jacobiSym (c * v) (n * t) : ℂ) =
      gaussPhaseA * (gaussRowFactor c n * gaussRowFactor c t) * (jacobiSym v (n * t) : ℂ) +
      gaussPhaseB * (gaussRowFactor (-c) n * gaussRowFactor (-c) t) * (jacobiSym v (n * t) : ℂ) := by
  have hn0 := Nat.pos_of_ne_zero hns.ne_zero
  have ht0 := Nat.pos_of_ne_zero hts.ne_zero
  let : NeZero (n * t) := ⟨mul_ne_zero hn0.ne' ht0.ne'⟩
  rw [jacobiGaussRatio_mul_jacobi (hn.mul ht) (Nat.squarefree_mul_iff.mpr ⟨hnt, hns, hts⟩),
    gaussRowFactor_mul c hn0 ht0, gaussRowFactor_mul (-c) hn0 ht0]

noncomputable def gaussProductDivisorJacobiRow (S T : Finset ℕ) (a b : ℕ → ℂ)
    (c : ℤ) (d : ℕ) (v : ℤ) : ℂ :=
  ∑ n ∈ S, ∑ t ∈ T, if Nat.Coprime n t ∧ d ∣ n * t then
    a n * b t * (jacobiGaussRatio (n * t) * (jacobiSym (c * v) (n * t) : ℂ)) else 0

theorem gaussProductDivisorJacobiRow_eq_two_rows (S T : Finset ℕ) (a b : ℕ → ℂ)
    (c : ℤ) (d : ℕ) (v : ℤ)
    (hS : ∀ n ∈ S, Odd n ∧ Squarefree n) (hT : ∀ t ∈ T, Odd t ∧ Squarefree t) :
    gaussProductDivisorJacobiRow S T a b c d v =
      gaussPhaseA * coprimeProductDivisorJacobiRow S T
        (gaussRowCoefficients c a) (gaussRowCoefficients c b) d v +
      gaussPhaseB * coprimeProductDivisorJacobiRow S T
        (gaussRowCoefficients (-c) a) (gaussRowCoefficients (-c) b) d v := by
  unfold gaussProductDivisorJacobiRow coprimeProductDivisorJacobiRow
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hp : Nat.Coprime n t ∧ d ∣ n * t
  · rw [ite_eq_left hp, ite_eq_left hp, ite_eq_left hp,
      gauss_ratio_product_row (hS n hn).1 (hT t ht).1 (hS n hn).2 (hT t ht).2 hp.1]
    unfold gaussRowCoefficients
    ring
  · simp only [ite_eq_right hp, mul_zero, add_zero]

end Ostmann.QuadraticSieve

end OAI
