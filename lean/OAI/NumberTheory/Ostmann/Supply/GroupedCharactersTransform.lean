import OAI.NumberTheory.Ostmann.Supply.TruncatedWeight
import OAI.NumberTheory.Ostmann.Tree.MellinTransform

namespace OAI

noncomputable section
namespace Ostmann.Supply.GroupedCharacters
open Finset Ostmann.FiniteField
open scoped BigOperators ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
local instance (i : ι) : Fintype (MulChar (F i) ℂ) := Fintype.ofFinite _

def unitCharacter (ρ : ∀ i, MulChar (F i) ℂ) (x : ∀ i, (F i)ˣ) : ℂ := ∏ i, ρ i (x i)

def coefficient (f : (∀ i, (F i)ˣ) → ℂ) (ρ : ∀ i, MulChar (F i) ℂ) : ℂ :=
  (Fintype.card (∀ i, (F i)ˣ) : ℂ)⁻¹ * ∑ x, f x * conj (unitCharacter F ρ x)

omit [DecidableEq ι] [∀ index, Fintype (F index)] [∀ index, DecidableEq (F index)] in
@[simp] theorem unitCharacter_one (x : ∀ i, (F i)ˣ) : unitCharacter F 1 x = 1 := by
  simp [unitCharacter]

omit [DecidableEq ι] in
@[simp] theorem norm_unitCharacter (ρ : ∀ i, MulChar (F i) ℂ) (x : ∀ i, (F i)ˣ) :
    ‖unitCharacter F ρ x‖ = 1 := by
  simp only [unitCharacter, norm_prod, mulChar_norm_unit, prod_const_one]

theorem coefficient_one (f : (∀ i, (F i)ˣ) → ℂ) :
    coefficient F f 1 = (Fintype.card (∀ i, (F i)ˣ) : ℂ)⁻¹ * ∑ x, f x := by
  simp only [coefficient, unitCharacter_one, map_one, mul_one]

theorem unitCharacter_kernel (x y : ∀ i, (F i)ˣ) :
    (∑ ρ : ∀ i, MulChar (F i) ℂ, conj (unitCharacter F ρ x) * unitCharacter F ρ y) =
      if x = y then (Fintype.card (∀ i, (F i)ˣ) : ℂ) else 0 := by
  simp only [unitCharacter, map_prod, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (χ : MulChar (F i) ℂ) => conj (χ (x i)) * χ (y i))]
  simp_rw [sum_mulChar_kernel]
  by_cases h : x = y
  · subst y
    simp [Fintype.card_pi]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra! hn
      exact h (funext hn)
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

theorem inversion (f : (∀ i, (F i)ˣ) → ℂ) (y : ∀ i, (F i)ˣ) :
    (∑ ρ : ∀ i, MulChar (F i) ℂ, coefficient F f ρ * unitCharacter F ρ y) = f y := by
  simp only [coefficient, sum_mul, mul_assoc, mul_sum]
  rw [sum_comm]
  conv_lhs => arg 2; ext x; rw [← mul_sum, ← mul_sum, unitCharacter_kernel]
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
  have hN : (Fintype.card (∀ i, (F i)ˣ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

theorem norm_coefficient_le_mean (f : (∀ i, (F i)ˣ) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ρ : ∀ i, MulChar (F i) ℂ) :
    ‖coefficient F (fun x => (f x : ℂ)) ρ‖ ≤
      (Fintype.card (∀ i, (F i)ˣ) : ℝ)⁻¹ * ∑ x, f x := by
  rw [coefficient, norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    _ ≤ ∑ x, ‖(f x : ℂ) * conj (unitCharacter F ρ x)‖ := norm_sum_le _ _
    _ = ∑ x, f x := by
      apply sum_congr rfl
      intro x hx
      simp only [norm_mul, Complex.norm_conj, norm_unitCharacter, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf x)]

theorem coefficient_prod (f : ∀ i, (F i)ˣ → ℂ) (ρ : ∀ i, MulChar (F i) ℂ) :
    coefficient F (fun x => ∏ i, f i (x i)) ρ = ∏ i, mellin (f i) (ρ i) := by
  simp only [coefficient, unitCharacter, map_prod, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (x : (F i)ˣ) => f i x * conj (ρ i x))]
  simp only [Ostmann.FiniteField.mellin, prod_mul_distrib, Fintype.card_pi, Nat.cast_prod, prod_inv_distrib]

theorem coefficient_sum {α : Type*} (s : Finset α) (f : α → (∀ i, (F i)ˣ) → ℂ)
    (ρ : ∀ i, MulChar (F i) ℂ) :
    coefficient F (fun x => ∑ a ∈ s, f a x) ρ = ∑ a ∈ s, coefficient F (f a) ρ := by
  simp only [coefficient, sum_mul, mul_sum]
  rw [sum_comm]

def weightCoefficient (b : ∀ i, F i → ℝ) (K : ℕ) (ρ : ∀ i, MulChar (F i) ℂ) : ℂ :=
  coefficient F (fun x => (truncatedWeight univ (fun i => b i (x i)) K : ℂ)) ρ

theorem weight_expansion (b : ∀ i, F i → ℝ) (K : ℕ) (x : ∀ i, (F i)ˣ) :
    (truncatedWeight univ (fun i => b i (x i)) K : ℂ) =
      ∑ ρ : ∀ i, MulChar (F i) ℂ, weightCoefficient F b K ρ * unitCharacter F ρ x :=
  (inversion F (fun x => (truncatedWeight univ (fun i => b i (x i)) K : ℂ)) x).symm

theorem norm_weightCoefficient_le_mean (b : ∀ i, F i → ℝ) (K : ℕ)
    (ρ : ∀ i, MulChar (F i) ℂ) :
    ‖weightCoefficient F b K ρ‖ ≤
      (Fintype.card (∀ i, (F i)ˣ) : ℝ)⁻¹ *
        ∑ x : ∀ i, (F i)ˣ, truncatedWeight univ (fun i => b i (x i)) K :=
  norm_coefficient_le_mean F _ (fun _ => truncatedWeight_nonneg _ _ _) ρ

end Ostmann.Supply.GroupedCharacters

end

end OAI
