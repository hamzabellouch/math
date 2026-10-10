import OAI.Analysis.Cotype.Fourier
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def biasWeight (t : ι → ℝ) (ε : ι → Bool) : ℝ :=
  ∏ i, (1 + t i * sign (ε i)) / 2

def biasedExpectation (f : (ι → Bool) → ℝ) (t : ι → ℝ) : ℝ :=
  ∑ ε, biasWeight t ε * f ε

theorem biasedExpectation_const_mul (f : (ι → Bool) → ℝ) (t : ι → ℝ) (a : ℝ) :
    biasedExpectation (fun ε => a * f ε) t = a * biasedExpectation f t := by
  simp only [biasedExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε _
  ring

theorem biasedExpectation_mul_const (f : (ι → Bool) → ℝ) (t : ι → ℝ) (a : ℝ) :
    biasedExpectation (fun ε => f ε * a) t = biasedExpectation f t * a := by
  simpa only [mul_comm] using biasedExpectation_const_mul f t a

theorem biasedExpectation_sum {α : Type*} [Fintype α]
    (f : α → (ι → Bool) → ℝ) (t : ι → ℝ) :
    biasedExpectation (fun ε => ∑ a, f a ε) t = ∑ a, biasedExpectation (f a) t := by
  simp only [biasedExpectation, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem biasWeight_sum (t : ι → ℝ) : (∑ ε, biasWeight t ε) = 1 := by
  unfold biasWeight
  rw [← Fintype.prod_sum (fun i (b : Bool) => (1 + t i * sign b) / 2)]
  have he (i) : (∑ b : Bool, (1 + t i * sign b) / 2) = (1 : ℝ) := by
    simp only [Fintype.sum_bool, sign_true, sign_false]
    ring
  simp_rw [he]
  simp

omit [DecidableEq ι] in
theorem biasWeight_nonneg {t : ι → ℝ} (ht : ∀ i, |t i| ≤ 1) (ε : ι → Bool) :
    0 ≤ biasWeight t ε := by
  apply Finset.prod_nonneg
  intro i _
  obtain ⟨hl, hu⟩ := abs_le.mp (ht i)
  cases ε i <;> simp only [sign_false, sign_true] <;> linarith

theorem biasedExpectation_bound {f : (ι → Bool) → ℝ} {t : ι → ℝ} {M : ℝ}
    (ht : ∀ i, |t i| ≤ 1) (hf : ∀ ε, |f ε| ≤ M) :
    |biasedExpectation f t| ≤ M := by
  unfold biasedExpectation
  calc
    _ ≤ ∑ ε, |biasWeight t ε * f ε| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ε, biasWeight t ε * |f ε| := by
      apply Finset.sum_congr rfl
      intro ε _
      rw [abs_mul, abs_of_nonneg (biasWeight_nonneg ht ε)]
    _ ≤ ∑ ε, biasWeight t ε * M := Finset.sum_le_sum (fun ε _ =>
      mul_le_mul_of_nonneg_left (hf ε) (biasWeight_nonneg ht ε))
    _ = M := by rw [← Finset.sum_mul, biasWeight_sum, one_mul]

theorem biasedExpectation_character (t : ι → ℝ) (p : ι → Bool) :
    biasedExpectation (character p) t = ∏ i, if p i then t i else 1 := by
  unfold biasedExpectation biasWeight character
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) =>
    ((1 + t i * sign b) / 2) * (if p i then sign b else 1))]
  apply Finset.prod_congr rfl
  intro i _
  cases p i <;> simp only [Fintype.sum_bool, sign_false, sign_true, Bool.false_eq_true,
    ite_false, ite_true] <;> ring

theorem biasedExpectation_fourier (f : (ι → Bool) → ℝ) (t : ι → ℝ) :
    biasedExpectation f t = ∑ p, fourier f p * ∏ i, if p i then t i else 1 := by
  calc
    biasedExpectation f t = ∑ ε, biasWeight t ε *
        ∑ p, fourier f p * character p ε := by simp only [fourier_inversion, biasedExpectation]
    _ = ∑ p, fourier f p * biasedExpectation (character p) t := by
      simp only [biasedExpectation, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro ε _
      ring
    _ = _ := by simp_rw [biasedExpectation_character]

theorem biasedExpectation_common_mean (f : (ι → Bool) → ℝ) (t : ℝ) :
    biasedExpectation f (fun _ => t) =
      ∑ p, fourier f p * t ^ (Finset.univ.filter (fun i => p i = true)).card := by
  rw [biasedExpectation_fourier]
  simp [← Finset.prod_filter]

theorem fourier_generating_bound {f : (ι → Bool) → ℝ} {M t : ℝ}
    (ht : |t| ≤ 1) (hf : ∀ ε, |f ε| ≤ M) :
    |∑ p, fourier f p * t ^ (Finset.univ.filter (fun i => p i = true)).card| ≤ M := by
  rw [← biasedExpectation_common_mean]
  exact biasedExpectation_bound (fun _ => ht) hf

end Cotype

end

end OAI
