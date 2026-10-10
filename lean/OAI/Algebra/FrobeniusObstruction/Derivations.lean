import Mathlib
import OAI.Algebra.FrobeniusObstruction.Coordinates

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k S : Type*} [Fintype ι] [DecidableEq ι] [CommRing k]
  [CommRing S] [Algebra k S] (ell : ℕ)

                                                                          
                                                                                     
theorem relativeDeriv_ext (f : Ring (ι := ι) (k := k) ell →ₐ[k] S)
    (u v : Ring (ι := ι) (k := k) ell →ₗ[k] S)
    (hu1 : u 1 = 0) (hv1 : v 1 = 0)
    (hu : ∀ x y, u (x*y) = u x * f y + f x * u y)
    (hv : ∀ x y, v (x*y) = v x * f y + f x * v y)
    (h : ∀ i, u (coordinate ell i) = v (coordinate ell i)) : u = v := by
  let X : ι → Ring (ι := ι) (k := k) ell := coordinate ell
  have hp (i : ι) (r : ℕ) : u (X i ^ r) = v (X i ^ r) := by
    induction r with
    | zero => exact hu1.trans hv1.symm
    | succ r hr =>
      rw [pow_succ, hu, hv, hr, h i]
  have hm (s : Finset ι) (p : ι → ℕ) :
      u (∏ i ∈ s, X i ^ p i) = v (∏ i ∈ s, X i ^ p i) := by
    induction s using Finset.induction_on with
    | empty => exact hu1.trans hv1.symm
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, hu, hv, hp, ih]
  apply LinearMap.ext
  intro x
  rw [monomial_expansion ell x, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul, map_smul, monomial_eq_prod]
  congr 1
  simpa only [monomial_eq_prod, Finsupp.prod, X] using hm _ (exponent ell a)

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [CharP k ell]

@[simp] theorem partial_include_left (i : ι) (a : Ring (ι := ι) (k := k) ell) :
    partialDeriv ell (Sum.inl i : ι ⊕ κ)
      (includeVariables (k := k) ell Sum.inl a) =
    includeVariables (k := k) ell Sum.inl (partialDeriv ell i a) := by
  let f : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι ⊕ κ) (k := k) ell :=
    includeVariables ell Sum.inl
  have H : (partialDeriv (k := k) ell (Sum.inl i : ι ⊕ κ)).toLinearMap.comp f.toLinearMap =
      f.toLinearMap.comp (partialDeriv ell i).toLinearMap := by
    apply relativeDeriv_ext ell f
    · simp
    · simp
    · intro x y
      simp only [LinearMap.comp_apply, Derivation.coeFn_coe, AlgHom.toLinearMap_apply,
        map_mul, Derivation.leibniz, smul_eq_mul]
      ring
    · intro x y
      simp only [LinearMap.comp_apply, Derivation.coeFn_coe, AlgHom.toLinearMap_apply,
        Derivation.leibniz, smul_eq_mul, map_add, map_mul]
      ring
    · intro j
      simp only [LinearMap.comp_apply, Derivation.coeFn_coe, AlgHom.toLinearMap_apply,
        f, includeVariables_coordinate]
      simp only [coordinate, partial_coordinate, Sum.inl.injEq]
      split_ifs <;> simp
  exact LinearMap.congr_fun H a

@[simp] theorem partial_include_left_other (j : κ) (a : Ring (ι := ι) (k := k) ell) :
    partialDeriv ell (Sum.inr j : ι ⊕ κ)
      (includeVariables (k := k) ell Sum.inl a) = 0 := by
  let f : Ring (ι := ι) (k := k) ell →ₐ[k] Ring (ι := ι ⊕ κ) (k := k) ell :=
    includeVariables ell Sum.inl
  have H : (partialDeriv (k := k) ell (Sum.inr j : ι ⊕ κ)).toLinearMap.comp f.toLinearMap = 0 := by
    apply relativeDeriv_ext ell f
    · simp
    · rfl
    · intro x y
      simp only [LinearMap.comp_apply, Derivation.coeFn_coe, AlgHom.toLinearMap_apply,
        map_mul, Derivation.leibniz, smul_eq_mul]
      ring
    · intros; simp
    · intro i
      simp only [LinearMap.comp_apply, Derivation.coeFn_coe, AlgHom.toLinearMap_apply,
        f, includeVariables_coordinate, LinearMap.zero_apply]
      simp only [coordinate, partial_coordinate, Sum.inr_ne_inl, ↓reduceIte]
  exact LinearMap.congr_fun H a

@[simp] theorem partial_include_right (i : κ) (a : Ring (ι := κ) (k := k) ell) :
    partialDeriv ell (Sum.inr i : ι ⊕ κ)
      (includeVariables (k := k) ell Sum.inr a) =
    includeVariables (k := k) ell Sum.inr (partialDeriv ell i a) := by
  let f : Ring (ι := κ) (k := k) ell →ₐ[k] Ring (ι := ι ⊕ κ) (k := k) ell :=
    includeVariables ell Sum.inr
  have H : (partialDeriv (k := k) ell (Sum.inr i : ι ⊕ κ)).toLinearMap.comp f.toLinearMap =
      f.toLinearMap.comp (partialDeriv ell i).toLinearMap := by
    apply relativeDeriv_ext ell f
    · simp
    · simp
    · intro x y
      simp only [LinearMap.comp_apply, Derivation.coeFn_coe, AlgHom.toLinearMap_apply,
        map_mul, Derivation.leibniz, smul_eq_mul]
      ring
    · intro x y
      simp only [LinearMap.comp_apply, Derivation.coeFn_coe, AlgHom.toLinearMap_apply,
        Derivation.leibniz, smul_eq_mul, map_add, map_mul]
      ring
    · intro j
      simp only [LinearMap.comp_apply, Derivation.coeFn_coe, AlgHom.toLinearMap_apply,
        f, includeVariables_coordinate]
      simp only [coordinate, partial_coordinate, Sum.inr.injEq]
      split_ifs <;> simp
  exact LinearMap.congr_fun H a

@[simp] theorem partial_include_right_other (j : ι) (a : Ring (ι := κ) (k := k) ell) :
    partialDeriv ell (Sum.inl j : ι ⊕ κ)
      (includeVariables (k := k) ell Sum.inr a) = 0 := by
  let f : Ring (ι := κ) (k := k) ell →ₐ[k] Ring (ι := ι ⊕ κ) (k := k) ell :=
    includeVariables ell Sum.inr
  have H : (partialDeriv (k := k) ell (Sum.inl j : ι ⊕ κ)).toLinearMap.comp f.toLinearMap = 0 := by
    apply relativeDeriv_ext ell f
    · simp
    · rfl
    · intro x y
      simp only [LinearMap.comp_apply, Derivation.coeFn_coe, AlgHom.toLinearMap_apply,
        map_mul, Derivation.leibniz, smul_eq_mul]
      ring
    · intros; simp
    · intro i
      simp only [LinearMap.comp_apply, Derivation.coeFn_coe, AlgHom.toLinearMap_apply,
        f, includeVariables_coordinate, LinearMap.zero_apply]
      simp only [coordinate, partial_coordinate, Sum.inl_ne_inr, ↓reduceIte]
  exact LinearMap.congr_fun H a

end BoundaryOnly.FormalObstruction.Frobenius

end

end OAI
