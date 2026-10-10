import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialIntegerGrid

namespace OAI

/-! # Polynomial maps of lattices extend as group maps

Multiplication identities on integral coordinates determine the identity on
all real coordinates. Polynomial inverse identities extend in the same way.
-/

noncomputable section
namespace PolycyclicRecognition
variable {I J : Type*} [gI : Group (I → ℝ)] [gJ : Group (J → ℝ)]

local instance sourcePolynomialGroupMul : Mul (I → ℝ) := gI.toMul
local instance sourcePolynomialGroupOne : One (I → ℝ) := gI.toOne
local instance targetPolynomialGroupMul : Mul (J → ℝ) := gJ.toMul
local instance targetPolynomialGroupOne : One (J → ℝ) := gJ.toOne
local instance sourcePolynomialGroupMonoid : Monoid (I → ℝ) := gI.toMonoid
local instance sourcePolynomialGroupMulOneClass : MulOneClass (I → ℝ) := gI.toMulOneClass
local instance targetPolynomialGroupMonoid : Monoid (J → ℝ) := gJ.toMonoid
local instance targetPolynomialGroupMulOneClass : MulOneClass (J → ℝ) := gJ.toMulOneClass

theorem coordinatePolynomial_mul_of_integer_mul
    {f : (I → ℝ) → (J → ℝ)} (hf : IsCoordinatePolynomial f)
    (hI : IsCoordinatePolynomial
      (fun p : (I ⊕ I) → ℝ => (p ∘ Sum.inl) * (p ∘ Sum.inr)))
    (hJ : IsCoordinatePolynomial
      (fun p : (J ⊕ J) → ℝ => (p ∘ Sum.inl) * (p ∘ Sum.inr)))
    (h : ∀ x y : I → ℤ,
      f ((fun i => (x i : ℝ)) * (fun i => (y i : ℝ))) =
        f (fun i => (x i : ℝ)) * f (fun i => (y i : ℝ))) :
    ∀ x y : I → ℝ, f (x * y) = f x * f y := by
  have hl := hf.comp hI
  have hp := (hf.comp (IsCoordinatePolynomial.reindex (Sum.inl : I → I ⊕ I))).pair
    (hf.comp (IsCoordinatePolynomial.reindex (Sum.inr : I → I ⊕ I)))
  have hr := hJ.comp hp
  have heq : (fun p : (I ⊕ I) → ℝ => f ((p ∘ Sum.inl) * (p ∘ Sum.inr))) =
      (fun p : (I ⊕ I) → ℝ => f (p ∘ Sum.inl) * f (p ∘ Sum.inr)) := by
    apply IsCoordinatePolynomial.ext_integer_grid hl hr
    intro z
    exact h (z ∘ Sum.inl) (z ∘ Sum.inr)
  intro x y
  have hh := congrFun heq (Sum.elim x y)
  simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr] using hh

def coordinatePolynomialHomFromIntegerGrid
    {f : (I → ℝ) → (J → ℝ)} (hf : IsCoordinatePolynomial f)
    (hI : IsCoordinatePolynomial
      (fun p : (I ⊕ I) → ℝ => (p ∘ Sum.inl) * (p ∘ Sum.inr)))
    (hJ : IsCoordinatePolynomial
      (fun p : (J ⊕ J) → ℝ => (p ∘ Sum.inl) * (p ∘ Sum.inr)))
    (h : ∀ x y : I → ℤ,
      f ((fun i => (x i : ℝ)) * (fun i => (y i : ℝ))) =
        f (fun i => (x i : ℝ)) * f (fun i => (y i : ℝ))) :
    (I → ℝ) →* (J → ℝ) where
  toFun := f
  map_one' := by
    have hh := coordinatePolynomial_mul_of_integer_mul hf hI hJ h 1 1
    rw [one_mul] at hh
    exact (mul_left_cancel ((mul_one (f 1)).trans hh)).symm
  map_mul' := coordinatePolynomial_mul_of_integer_mul hf hI hJ h

omit gI gJ in
theorem coordinatePolynomial_leftInverse_of_integer
    {f : (I → ℝ) → (J → ℝ)} {g : (J → ℝ) → (I → ℝ)}
    (hf : IsCoordinatePolynomial f) (hg : IsCoordinatePolynomial g)
    (h : ∀ x : I → ℤ, g (f (fun i => (x i : ℝ))) = (fun i => (x i : ℝ))) :
    Function.LeftInverse g f := by
  have hi := IsCoordinatePolynomial.reindex (id : I → I)
  have heq : g ∘ f = id :=
    (hg.comp hf).ext_integer_grid hi h
  exact congrFun heq

def coordinatePolynomialEquivFromIntegerGrid
    {f : (I → ℝ) → (J → ℝ)} {g : (J → ℝ) → (I → ℝ)}
    (hf : IsCoordinatePolynomial f) (hg : IsCoordinatePolynomial g)
    (hI : IsCoordinatePolynomial
      (fun p : (I ⊕ I) → ℝ => (p ∘ Sum.inl) * (p ∘ Sum.inr)))
    (hJ : IsCoordinatePolynomial
      (fun p : (J ⊕ J) → ℝ => (p ∘ Sum.inl) * (p ∘ Sum.inr)))
    (hmul : ∀ x y : I → ℤ,
      f ((fun i => (x i : ℝ)) * (fun i => (y i : ℝ))) =
        f (fun i => (x i : ℝ)) * f (fun i => (y i : ℝ)))
    (hleft : ∀ x : I → ℤ, g (f (fun i => (x i : ℝ))) = (fun i => (x i : ℝ)))
    (hright : ∀ y : J → ℤ, f (g (fun j => (y j : ℝ))) = (fun j => (y j : ℝ))) :
    (I → ℝ) ≃* (J → ℝ) where
  toFun := f
  invFun := g
  left_inv := coordinatePolynomial_leftInverse_of_integer hf hg hleft
  right_inv := coordinatePolynomial_leftInverse_of_integer hg hf hright
  map_mul' := coordinatePolynomial_mul_of_integer_mul hf hI hJ hmul

end PolycyclicRecognition

end

end OAI
