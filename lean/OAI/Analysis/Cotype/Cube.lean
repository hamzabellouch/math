import OAI.Analysis.Cotype.Model

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
@[simp] theorem sign_false : sign false = 1 := rfl
@[simp] theorem sign_true : sign true = -1 := rfl
@[simp] theorem sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num
@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> norm_num

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def character (p ε : ι → Bool) : ℝ := ∏ i, if p i then sign (ε i) else 1

omit [DecidableEq ι] in
theorem character_symm (p ε : ι → Bool) : character p ε = character ε p := by
  apply Finset.prod_congr rfl
  intro i _
  cases p i <;> cases ε i <;> rfl

omit [DecidableEq ι] in
@[simp] theorem character_sq (p ε : ι → Bool) : character p ε * character p ε = 1 := by
  rw [character, ← Finset.prod_mul_distrib]
  have h : ∀ i, (if p i then sign (ε i) else 1) *
      (if p i then sign (ε i) else 1) = (1 : ℝ) := by
    intro i; cases p i <;> simp
  simp_rw [h]
  simp

theorem character_orthogonality (p q : ι → Bool) :
    (∑ ε : ι → Bool, character p ε * character q ε) =
      if p = q then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  simp only [character, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) =>
    (if p i then sign b else 1) * (if q i then sign b else 1))]
  have h : ∀ i, (∑ b : Bool, (if p i then sign b else 1) *
      (if q i then sign b else 1)) = if p i = q i then (2 : ℝ) else 0 := by
    intro i
    cases p i <;> cases q i <;> norm_num [Fintype.sum_bool]
  simp_rw [h]
  rw [Fintype.prod_ite_zero]
  have heq : (∀ i, p i = q i) ↔ p = q := funext_iff.symm
  simp only [heq]
  split_ifs <;> simp

theorem average_character_mul (p q : ι → Bool) :
    average (fun ε => character p ε * character q ε) = if p = q then 1 else 0 := by
  classical
  have hc : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := ι → Bool))
  simp only [average, smul_eq_mul, character_orthogonality]
  split_ifs <;> simp_all

def fourier (f : (ι → Bool) → ℝ) (p : ι → Bool) : ℝ :=
  average (fun ε => f ε * character p ε)

theorem fourier_inversion (f : (ι → Bool) → ℝ) (ε : ι → Bool) :
    (∑ p, fourier f p * character p ε) = f ε := by
  classical
  have hc : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := ι → Bool))
  have ho (η : ι → Bool) :
      (∑ p, character p η * character p ε) =
        if η = ε then (Fintype.card (ι → Bool) : ℝ) else 0 := by
    simp_rw [character_symm _ η, character_symm _ ε]
    exact character_orthogonality η ε
  calc
    (∑ p, fourier f p * character p ε) =
        (Fintype.card (ι → Bool) : ℝ)⁻¹ *
          ∑ η, f η * ∑ p, character p η * character p ε := by
      simp only [fourier, average, smul_eq_mul]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro η _
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = f ε := by simp [ho, mul_comm (f ε)]

theorem parseval (f : (ι → Bool) → ℝ) :
    (∑ p, fourier f p ^ 2) = average (fun ε => f ε ^ 2) := by
  classical
  calc
    (∑ p, fourier f p ^ 2) =
        ∑ p, fourier f p * ((Fintype.card (ι → Bool) : ℝ)⁻¹ *
          ∑ ε, f ε * character p ε) := by
      simp only [fourier, average, smul_eq_mul, pow_two]
    _ = (Fintype.card (ι → Bool) : ℝ)⁻¹ *
        ∑ ε, f ε * ∑ p, fourier f p * character p ε := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ε _
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = average (fun ε => f ε ^ 2) := by
      simp only [fourier_inversion, average, smul_eq_mul, pow_two]

end Cotype

end

end OAI
