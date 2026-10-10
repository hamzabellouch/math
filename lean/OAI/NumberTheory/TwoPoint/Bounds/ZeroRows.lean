import OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Rat.Cast.CharZero

namespace OAI

/-! The zero-row estimate used in the random-prime rank lemma. -/

namespace TwoPointCorrelations

open Finset Matrix

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]

noncomputable def rationalRows (B : Matrix ι ι ℤ) (S : Finset ι) :
    (ι → ℚ) →ₗ[ℚ] (S → ℚ) :=
  LinearMap.pi (fun i : S => (LinearMap.proj i.val).comp
    (B.map (Int.castRingHom ℚ)).mulVecLin)

lemma rationalRows_surjective (B : Matrix ι ι ℤ) (hB : B.det ≠ 0) (S : Finset ι) :
    Function.Surjective (rationalRows B S) := by
  have hdet : (B.map (Int.castRingHom ℚ)).det ≠ 0 := by
    change ((Int.castRingHom ℚ).mapMatrix B).det ≠ 0
    rw [← (Int.castRingHom ℚ).map_det]
    change (B.det : ℚ) ≠ 0
    exact_mod_cast hB
  have hu : IsUnit (B.map (Int.castRingHom ℚ)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hsurj := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  intro z
  let w : ι → ℚ := fun i => if hi : i ∈ S then z ⟨i, hi⟩ else 0
  obtain ⟨x, hx⟩ := hsurj w
  refine ⟨x, ?_⟩
  ext i
  change ((B.map (Int.castRingHom ℚ)) *ᵥ x) i.val = z i
  rw [hx]
  simp [w, i.property]

omit [DecidableEq ι] in
lemma rationalRows_eq_iff (B : Matrix ι ι ℤ) (S : Finset ι) (x y : ι → ℤ) :
    rationalRows B S (fun i => (x i : ℚ)) = rationalRows B S (fun i => (y i : ℚ)) ↔
      ∀ i ∈ S, (B *ᵥ (x - y)) i = 0 := by
  have hi (i : ι) :
      (((B *ᵥ (x - y)) i : ℤ) : ℚ) =
        ((B.map (Int.castRingHom ℚ)) *ᵥ (fun j => (x j : ℚ))) i -
          ((B.map (Int.castRingHom ℚ)) *ᵥ (fun j => (y j : ℚ))) i := by
    simp [Matrix.mulVec, dotProduct, mul_sub, sum_sub_distrib]
  constructor
  · intro h i hiS
    have hx := congrFun h ⟨i, hiS⟩
    change ((B.map (Int.castRingHom ℚ)) *ᵥ (fun j => (x j : ℚ))) i =
      ((B.map (Int.castRingHom ℚ)) *ᵥ (fun j => (y j : ℚ))) i at hx
    have hz : (((B *ᵥ (x - y)) i : ℤ) : ℚ) = 0 := by rw [hi, hx, sub_self]
    exact_mod_cast hz
  · intro h
    ext i
    change ((B.map (Int.castRingHom ℚ)) *ᵥ (fun j => (x j : ℚ))) i.val =
      ((B.map (Int.castRingHom ℚ)) *ᵥ (fun j => (y j : ℚ))) i.val
    apply sub_eq_zero.mp
    rw [← hi i.val, h i.val i.property]
    simp

/-- Any specified `a` rows of an invertible integral matrix vanish with
probability at most `α^a` under independent atoms bounded by `α`. -/
theorem FiniteLaw.zero_rows_probability
    (μ : ι → FiniteLaw A) (value : A → ℤ) (hvalue : Function.Injective value)
    (B : Matrix ι ι ℤ) (hB : B.det ≠ 0) (S : Finset ι) (y : ι → A)
    (α : ℝ) (hα : 0 ≤ α) (hatom : ∀ i x, (μ i).weight x ≤ α) :
    (FiniteLaw.independent μ).probability (fun x =>
      ∀ i ∈ S, (B *ᵥ ((fun j => value (x j)) - (fun j => value (y j)))) i = 0) ≤
        α ^ S.card := by
  have hv : Function.Injective (fun a => (value a : ℚ)) :=
    Int.cast_injective.comp hvalue
  have h := FiniteLaw.probability_linear_equations μ (fun a => (value a : ℚ)) hv
    (rationalRows B S) (rationalRows_surjective B hB S)
    (rationalRows B S (fun j => (value (y j) : ℚ))) α hα hatom
  simpa only [rationalRows_eq_iff, Fintype.card_coe] using h

end TwoPointCorrelations

end OAI
