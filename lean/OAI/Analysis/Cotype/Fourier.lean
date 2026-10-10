import OAI.Analysis.Cotype.Cube
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def negateCube (ε : ι → Bool) : ι → Bool := fun i => !(ε i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem negateCube_negateCube (ε : ι → Bool) :
    negateCube (negateCube ε) = ε := by funext i; simp [negateCube]

def negateEquiv : (ι → Bool) ≃ (ι → Bool) where
  toFun := negateCube
  invFun := negateCube
  left_inv := negateCube_negateCube
  right_inv := negateCube_negateCube

theorem average_negate {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : (ι → Bool) → E) : average (fun ε => f (negateCube ε)) = average f := by
  unfold average
  congr 1
  exact Fintype.sum_equiv negateEquiv _ _ (fun _ => rfl)

def paritySign (p : ι → Bool) : ℝ := ∏ i, if p i then -1 else 1

omit [DecidableEq ι] in
theorem paritySign_eq (p : ι → Bool) :
    paritySign p = (-1 : ℝ) ^ (Finset.univ.filter (fun i => p i = true)).card := by
  simp [paritySign, ← Finset.prod_filter]

omit [DecidableEq ι] in
theorem character_negate (p ε : ι → Bool) :
    character p (negateCube ε) = paritySign p * character p ε := by
  unfold character paritySign
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases p i <;> simp [negateCube]

def oddPart (f : (ι → Bool) → ℝ) (ε : ι → Bool) : ℝ :=
  (f ε - f (negateCube ε)) / 2

def IsOdd (f : (ι → Bool) → ℝ) : Prop := ∀ ε, f (negateCube ε) = -f ε

omit [Fintype ι] [DecidableEq ι] in
theorem oddPart_isOdd (f : (ι → Bool) → ℝ) : IsOdd (oddPart f) := by
  intro ε
  simp only [oddPart, negateCube_negateCube]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem oddPart_eq_self {f : (ι → Bool) → ℝ} (hf : IsOdd f) : oddPart f = f := by
  funext ε
  dsimp [oddPart]
  rw [hf]
  ring

theorem fourier_negate (f : (ι → Bool) → ℝ) (p : ι → Bool) :
    fourier (fun ε => f (negateCube ε)) p = paritySign p * fourier f p := by
  rw [fourier, ← average_negate]
  simp only [negateCube_negateCube, character_negate]
  simp only [average, fourier, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ε _
  ring

theorem fourier_oddPart (f : (ι → Bool) → ℝ) (p : ι → Bool) :
    fourier (oddPart f) p = (1 - paritySign p) / 2 * fourier f p := by
  have h := fourier_negate f p
  simp only [fourier, average, smul_eq_mul] at h ⊢
  have he : (∑ ε, oddPart f ε * character p ε) =
      ((∑ ε, f ε * character p ε) -
        ∑ ε, f (negateCube ε) * character p ε) / 2 := by
    calc
      _ = ∑ ε, (f ε * character p ε -
          f (negateCube ε) * character p ε) / 2 := by
        apply Finset.sum_congr rfl
        intro ε _
        dsimp [oddPart]
        ring
      _ = _ := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul, Finset.sum_sub_distrib]
  rw [he]
  nlinarith [h]

theorem odd_even_coefficient_zero {f : (ι → Bool) → ℝ} (hf : IsOdd f)
    {p : ι → Bool} (hp : paritySign p = 1) : fourier f p = 0 := by
  have h := fourier_oddPart f p
  rw [oddPart_eq_self hf, hp] at h
  simpa using h

theorem oddPart_preserves_odd_coefficient (f : (ι → Bool) → ℝ)
    {p : ι → Bool} (hp : paritySign p = -1) :
    fourier (oddPart f) p = fourier f p := by
  rw [fourier_oddPart, hp]
  ring

end Cotype

end

end OAI
