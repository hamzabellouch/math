import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalCoprime

namespace OAI

noncomputable section
namespace Ostmann.Characters.TemplateSupportRemoval
open MvPolynomial
open Ostmann.Arithmetic.PolynomialFlagReplacementFinite
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def familyCoprimeSupportedValue {κ : Type*} (D : Finset κ) (mask : Bool)
    (p : ℕ) (y : κ → ℤ) (f : ℂ) : ℂ :=
  if mask then if ∀ j ∈ D, IsCoprime (p:ℤ) (y j) then f else 0 else 0

def familyPolynomialEnlargedValue {κ τ : Type*} (D : Finset κ)
    (P : κ → MvPolynomial τ ℤ) (mask : Bool) (f : ℂ) : ℂ :=
  if ∀ j ∈ D, P j ≠ 0 then if mask then f else 0 else 0

theorem family_coprime_enlargement_pointwise {ι κ : Type*} [DecidableEq ι]
    (i : ι) (D : Finset κ) (P : κ → MvPolynomial ι ℤ) (den y : κ → ℤ)
    (x : Other i → ℤ) (p : ℕ) (hp : p.Prime) (mask : Bool) (f : ℂ)
    {A : ℝ} (hA : 0 ≤ A) (hf : ‖f‖ ≤ A)
    (hclear : ∀ j ∈ D, mask=true → den j*y j=eval (insertCoordinate i x (p:ℤ)) (P j))
    (hden : ∀ j ∈ D, mask=true → IsCoprime (p:ℤ) (den j)) :
    ‖familyCoprimeSupportedValue D mask p y f-
      familyPolynomialEnlargedValue D (fun j => eraseCoordinate i (P j)) mask f‖ ≤
      if mask then A*(∑ j ∈ D, flagError (eraseCoordinate i (P j)) x p) else 0 := by
  classical
  cases mask with
  | false => simp [familyCoprimeSupportedValue,familyPolynomialEnlargedValue]
  | true =>
    simp only [familyCoprimeSupportedValue,familyPolynomialEnlargedValue,ite_true]
    have hnonneg : 0 ≤ A*(∑ j ∈ D, flagError (eraseCoordinate i (P j)) x p) :=
      mul_nonneg hA (Finset.sum_nonneg (fun j _ => flagError_nonneg _ _ _))
    have hiff (j : κ) (hj : j ∈ D) := erased_dvd_iff_not_isCoprime i (P j) x p hp
      (den j) (y j) (hclear j hj rfl) (hden j hj rfl)
    by_cases hP : ∀ j ∈ D, eraseCoordinate i (P j) ≠ 0
    · by_cases hc : ∀ j ∈ D, IsCoprime (p:ℤ) (y j)
      · rw [ite_eq_left hc,ite_eq_left hP,sub_self,norm_zero]
        exact hnonneg
      · have hnot := hc
        push Not at hc
        obtain ⟨j,hj,hjc⟩ := hc
        have hd := (hiff j hj).mpr hjc
        have hflag : flagError (eraseCoordinate i (P j)) x p=1 := by
          simp [flagError,divisibilityIndicator,hP j hj,hd]
        have hsum : 1 ≤ ∑ u ∈ D, flagError (eraseCoordinate i (P u)) x p := by
          rw [← hflag]
          exact Finset.single_le_sum (fun u _ => flagError_nonneg (eraseCoordinate i (P u)) x p) hj
        have hh := hf.trans (by simpa using mul_le_mul_of_nonneg_left hsum hA)
        rw [ite_eq_right hnot,ite_eq_left hP,zero_sub,norm_neg]
        exact hh
    · push Not at hP
      obtain ⟨j,hj,hjzero⟩ := hP
      have hnc : ¬IsCoprime (p:ℤ) (y j) := (hiff j hj).mp (by simp [hjzero])
      have hfalse : ¬∀ u ∈ D, IsCoprime (p:ℤ) (y u) := fun h => hnc (h j hj)
      have hfalseP : ¬∀ u ∈ D, eraseCoordinate i (P u)≠0 := fun h => h j hj hjzero
      rw [ite_eq_right hfalse,ite_eq_right hfalseP,sub_self,norm_zero]
      exact hnonneg

end Ostmann.Characters.TemplateSupportRemoval

end

end OAI
