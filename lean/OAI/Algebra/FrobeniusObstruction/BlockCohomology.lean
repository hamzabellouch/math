import Mathlib
import OAI.Algebra.FrobeniusObstruction.MixedForms
import OAI.Algebra.FrobeniusObstruction.Retractions

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.BlockCohomology
open MixedForms SquareZero
variable {k A ι : Type*} [Field k] [CommRing A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]
variable (pd : ι → Derivation k A A) (q : A)
variable (hcomm : ∀ i j a, pd i (pd j a) = pd j (pd i a))

abbrev H := Cohomology (delta pd q) (delta_sq pd q)

theorem delta_parity (x : Forms (k := k) (A := A) (ι := ι)) :
    delta pd q (parity x) = -parity (delta pd q x) := by
  simp only [delta_apply, map_mul, parity_gradient, neg_mul, neg_neg]

include hcomm in
theorem delta_d (x : Forms (k := k) (A := A) (ι := ι)) :
    delta pd q (d pd x) = -d pd (delta pd q x) :=
  eq_neg_of_add_eq_zero_right (d_delta pd hcomm q x)

def P : Module.End k (H pd q) :=
  oddInduced (delta pd q) (delta_sq pd q) parity.toLinearMap (delta_parity pd q)

def D : Module.End k (H pd q) :=
  oddInduced (delta pd q) (delta_sq pd q) (d pd) (delta_d pd q hcomm)

def coefficient (s : A) : Module.End k (Forms (k := k) (A := A) (ι := ι)) :=
  (Algebra.lmul k _).toLinearMap (coeff s)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem coefficient_apply (s : A) (x : Forms (k := k) (A := A) (ι := ι)) :
    coefficient s x = coeff s * x := rfl

theorem delta_coefficient (s : A) (x : Forms (k := k) (A := A) (ι := ι)) :
    delta pd q (coefficient s x) = coefficient s (delta pd q x) := by
  simp only [coefficient_apply, delta_apply]
  rw [← mul_assoc, ← coeff_commute, mul_assoc]

def S (s : A) : Module.End k (H pd q) :=
  evenInduced (delta pd q) (delta_sq pd q) (coefficient s) (delta_coefficient pd q s)

theorem P_sq (x : H pd q) : P pd q (P pd q x) = x := by
  obtain ⟨z,rfl⟩ := classMap_surjective (delta pd q) (delta_sq pd q) x
  change classMap _ _ (cycleMap _ _ _ _ (cycleMap _ _ _ _ z)) = classMap _ _ z
  congr 1
  exact Subtype.ext (parity_sq (z : Forms (k := k) (A := A) (ι := ι)))

theorem D_sq (x : H pd q) : D pd q hcomm (D pd q hcomm x) = 0 :=
  oddInduced_square_zero (delta pd q) (delta_sq pd q) (d pd) (delta_d pd q hcomm)
    (d_sq pd hcomm) x

theorem D_P (x : H pd q) : D pd q hcomm (P pd q x) = -P pd q (D pd q hcomm x) := by
  obtain ⟨z,rfl⟩ := classMap_surjective (delta pd q) (delta_sq pd q) x
  change classMap _ _ (cycleMap _ _ _ _ (cycleMap _ _ _ _ z)) =
    -classMap _ _ (cycleMap _ _ _ _ (cycleMap _ _ _ _ z))
  rw [← map_neg]
  congr 1
  exact Subtype.ext (d_parity pd (z : Forms (k := k) (A := A) (ι := ι)))

theorem S_P (s : A) (x : H pd q) : S pd q s (P pd q x) = P pd q (S pd q s x) := by
  obtain ⟨z,rfl⟩ := classMap_surjective (delta pd q) (delta_sq pd q) x
  change classMap _ _ (cycleMap _ _ _ _ (cycleMap _ _ _ _ z)) =
    classMap _ _ (cycleMap _ _ _ _ (cycleMap _ _ _ _ z))
  congr 1
  apply Subtype.ext
  change coeff s * parity (z : Forms (k := k) (A := A) (ι := ι)) = parity (coeff s * (z : Forms (k := k) (A := A) (ι := ι)))
  rw [map_mul, parity_coeff]

                                                                           
                                                                    
theorem retraction (htwo : (2 : k) ≠ 0) (s : A) :
    ∃ r h : Module.End k (H pd q),
      (∀ x, D pd q hcomm (r x) = r (D pd q hcomm x)) ∧
      (∀ x, P pd q (r x) = r (P pd q x)) ∧
      (∀ x, P pd q (h x) = -h (P pd q x)) ∧
      (∀ x, x-r x = D pd q hcomm (h x) + h (D pd q hcomm x)) ∧
      (∀ x, S pd q s x = 0 → S pd q s (r x) = 0 ∧ S pd q s (D pd q hcomm (r x)) = 0) :=
  parity_retraction htwo (D pd q hcomm) (S pd q s) (P pd q)
    (D_sq pd q hcomm) (P_sq pd q) (D_P pd q hcomm) (S_P pd q s)

                                                                            
                                                
theorem correction (s : A) (x : Cycles (delta pd q))
    (hS : S pd q s (classMap _ (delta_sq pd q) x) = 0)
    (hSD : S pd q s (D pd q hcomm (classMap _ (delta_sq pd q) x)) = 0) :
    ∃ y, delta pd q y = -delta pd s x := by
  apply correction_of_kernel (delta pd q) (delta_sq pd q) (d pd)
    (coefficient s) (delta pd s) (delta_d pd q hcomm)
    (delta_coefficient pd q s) _ _ x hS hSD
  · intro z
    simp only [delta_apply]
    rw [← mul_assoc]
    have hanti : MixedForms.gradient pd q * MixedForms.gradient pd s =
        -(MixedForms.gradient pd s * MixedForms.gradient pd q) := by
      rw [gradient_supercommute, parity_gradient, neg_mul]
    rw [hanti, neg_mul, mul_assoc]
  · intro z
    exact d_commutator pd s z

end BoundaryOnly.FormalObstruction.BlockCohomology

end

end OAI
