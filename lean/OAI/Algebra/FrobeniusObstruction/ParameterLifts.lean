import Mathlib
import OAI.Algebra.FrobeniusObstruction.FixedResidue

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.MixedForms
variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable [Fintype ι] [DecidableEq ι]
open scoped TensorProduct

                                                                          
                                                                        
theorem gradient_mul_list_prod_zero (pd : ι → Derivation k A A) (q : A)
    (xs : List (Forms (k := k) (A := A) (ι := ι)))
    (x : Forms (k := k) (A := A) (ι := ι)) (hx : x ∈ xs)
    (hq : gradient pd q * x = 0) : gradient pd q * xs.prod = 0 := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst x
      rw [List.prod_cons, ← mul_assoc, hq, zero_mul]
    · rw [List.prod_cons, ← mul_assoc, gradient_supercommute, mul_assoc,
        ih h, mul_zero]

theorem gradient_constant (pd : ι → Derivation k A A) (s : A)
    (hs : ∀ i, pd i s = 0) : gradient pd s = 0 := by
  simp only [gradient_eq, hs, TensorProduct.zero_tmul, Finset.sum_const_zero]

theorem gradient_mul_constant (pd : ι → Derivation k A A) (s p : A)
    (hs : ∀ i, pd i s = 0) : gradient pd (s*p) = coeff s * gradient pd p := by
  change d pd (coeff (k := k) (ι := ι) (s*p)) = _
  rw [map_mul, d_mul, d_coeff, gradient_constant pd s hs, zero_mul, parity_coeff,
    d_coeff, zero_add]

theorem perturbed_factor (pd : ι → Derivation k A A) (Q p s : A)
    (hs : ∀ i, pd i s = 0) (hs2 : s*s = 0)
    (x y : Forms (k := k) (A := A) (ι := ι))
    (hx : gradient pd Q * x = 0)
    (hy : gradient pd Q * y = -(gradient pd p * x)) :
    gradient pd (Q+s*p) * (x+coeff s*y) = 0 := by
  have hg : gradient pd (Q+s*p) = gradient pd Q + coeff s * gradient pd p := by
    change d pd (coeff (k := k) (ι := ι) (Q+s*p)) = _
    rw [map_add, map_add, d_coeff, d_coeff, gradient_mul_constant pd s p hs]
  have hc (z : Forms (k := k) (A := A) (ι := ι)) : z * coeff s = coeff s * z :=
    (coeff_commute s z).symm
  rw [hg, add_mul, mul_add, mul_add, hx, zero_add,
    ← mul_assoc (gradient pd Q), hc, mul_assoc, hy,
    ← mul_assoc (coeff s * gradient pd p), mul_assoc (coeff s) (gradient pd p) (coeff s),
    hc, ← mul_assoc (coeff s) (coeff s), ← map_mul, hs2, map_zero, zero_mul,
    mul_neg, mul_assoc, zero_mul, add_zero, neg_add_cancel]

                                                                      
                                                                        
                                                     
theorem separated_parameter_lift {b : ℕ}
    (pd : ι → Derivation k A A) (Q p s : Fin b → A)
    (hs : ∀ j i, pd i (s j) = 0) (hs2 : ∀ j, s j * s j = 0)
    (x y : Fin b → Forms (k := k) (A := A) (ι := ι))
    (hx : ∀ j, gradient pd (Q j) * x j = 0)
    (hy : ∀ j, gradient pd (Q j) * y j = -(gradient pd (p j) * x j)) :
    delta pd (∑ j, (Q j + s j * p j))
      (List.ofFn (fun j => x j + coeff (s j) * y j)).prod = 0 := by
  change gradient pd (∑ j, (Q j + s j * p j)) * _ = 0
  have hg : gradient pd (∑ j, (Q j + s j * p j)) =
      ∑ j, gradient pd (Q j + s j * p j) := by
    change d pd (coeff (k := k) (ι := ι) (∑ j, (Q j + s j * p j))) = _
    rw [map_sum, map_sum]
    rfl
  rw [hg, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro j _
  apply gradient_mul_list_prod_zero pd (Q j + s j * p j)
    _ (x j + coeff (s j) * y j)
  · exact List.mem_ofFn.mpr ⟨j,rfl⟩
  · exact perturbed_factor pd (Q j) (p j) (s j) (hs j) (hs2 j) (x j) (y j) (hx j) (hy j)

end BoundaryOnly.FormalObstruction.MixedForms

namespace BoundaryOnly.FormalObstruction
variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B]

                                                                                  
                                                                             
                                        
def firstOrder (f : A →ₐ[k] B) (D : Derivation k A A) (s : B) (hs : s*s = 0) : A →ₐ[k] B where
  toFun x := f x + s * f (D x)
  map_one' := by simp only [map_one, Derivation.map_one_eq_zero, map_zero, mul_zero, add_zero]
  map_mul' x y := by
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add]
    linear_combination -(f (D x) * f (D y)) * hs
  map_zero' := by simp only [map_zero, mul_zero, add_zero]
  map_add' x y := by simp only [map_add]; ring
  commutes' r := by
    simp only [AlgHom.commutes, Derivation.map_algebraMap, map_zero, mul_zero, add_zero]

@[simp] theorem firstOrder_apply (f : A →ₐ[k] B) (D : Derivation k A A)
    (s : B) (hs : s*s = 0) (x : A) :
    firstOrder f D s hs x = f x + s*f (D x) := rfl
end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k S : Type*} [Fintype ι] [DecidableEq ι] [CommRing k]
variable [CommRing S] [Algebra k S] (ell : ℕ) [CharP k ell]

                                                                         
                                                                           
theorem evaluation_first_order (f g : Ring (ι := ι) (k := k) ell →ₐ[k] S)
    (j : ι) (s : S) (hs : s*s = 0)
    (hg : ∀ i, g (coordinate ell i) = f (coordinate ell i) + if j = i then s else 0)
    (x : Ring (ι := ι) (k := k) ell) :
    g x = f x + s*f (partialDeriv ell j x) := by
  have he : g = firstOrder f (partialDeriv ell j) s hs := by
    apply algHom_ext
    intro i
    rw [firstOrder_apply, hg, show partialDeriv ell j (coordinate ell i) =
      (if j = i then 1 else 0) from partial_coordinate ell j i]
    by_cases hi : j = i
    · simp only [ite_eq_left hi, map_one, mul_one]
    · simp only [ite_eq_right hi, map_zero, mul_zero]
  exact AlgHom.congr_fun he x
end BoundaryOnly.FormalObstruction.Frobenius

end

end OAI
