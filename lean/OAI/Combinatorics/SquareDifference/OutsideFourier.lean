import OAI.Combinatorics.SquareDifference.IntervalCounting

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference.PairBridge

open LiftTheory.SquareDifference

section Outside

variable {J : Type*} [instFintypeJ : Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)] (B : Finset J)

def outsideExtend (a : ResidueSpace (OutsideModulus p B)) : ResidueSpace p :=
  fun j => if hj : j∈B then 0 else a ⟨j,hj⟩

lemma outsideExtend_neg {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)]
    (B : Finset J) (a : ResidueSpace (OutsideModulus p B)) :
    outsideExtend p B (-a)= -(outsideExtend p B a) := by
  funext j
  simp only [outsideExtend, Pi.neg_apply]
  split_ifs <;> simp

lemma outsideExtend_disjoint {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)]
    (B : Finset J) (a : ResidueSpace (OutsideModulus p B)) :
    Disjoint (primeSupport p (outsideExtend p B a)) B := by
  apply disjoint_left.mpr
  intro j hj hB
  simp [primeSupport,outsideExtend,hB] at hj

lemma outsideExtend_char (a : ResidueSpace (OutsideModulus p B)) (x : ResidueSpace p) :
    prodChar p (outsideExtend p B a) x=prodChar (OutsideModulus p B) a (outsideCoordinate p B x) := by
  rw [prodChar_split p B]
  have ho : outsideCoordinate p B (outsideExtend p B a)=a := by
    funext j
    simp only [outsideCoordinate,outsideExtend,j.property,dite_false]
  have hr : rootCharacter p B (outsideExtend p B a) x=1 := by
    apply prod_eq_one
    intro j hj
    simp only [outsideExtend,hj,dite_true,zero_mul,AddChar.map_zero_eq_one]
  rw [hr,ho,one_mul]

lemma outsideExtend_denominator {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)]
    (B : Finset J) (a : ResidueSpace (OutsideModulus p B)) :
    supportDenominator p (outsideExtend p B a)=supportDenominator (OutsideModulus p B) a := by
  unfold supportDenominator primeSupport
  rw [prod_filter]
  have he : (∏j,if outsideExtend p B a j≠0 then p j else 1)=
      ∏j∈Bᶜ,if outsideExtend p B a j≠0 then p j else 1 := by
    symm
    apply prod_subset (subset_univ _)
    intro j _ hj
    have hB : j∈B := by simpa using hj
    simp [outsideExtend,hB]
  rw [he,prod_filter]
  rw [prod_subtype Bᶜ (fun j => mem_compl) (fun j => if outsideExtend p B a j≠0 then p j else 1)]
  apply prod_congr rfl
  intro j _
  simp only [outsideExtend,j.property,dite_false,OutsideModulus]

lemma expect_outside {E : Type*} [AddCommMonoid E] [Module ℚ≥0 E]
    (f : ResidueSpace (OutsideModulus p B) → E) :
    (𝔼 x : ResidueSpace p,f (outsideCoordinate p B x))=𝔼 y,f y := by
  let e := Equiv.piEquivPiSubtypeProd (fun j : J => j∈B) (fun j => ZMod (p j))
  rw [Fintype.expect_equiv e (fun x => f (outsideCoordinate p B x)) (fun x => f x.2) (fun _ => rfl)]
  rw [←univ_product_univ,expect_product]
  simp only [Fintype.expect_const]

noncomputable def assembleOutside (z : ResidueSpace p) (x : ResidueSpace (OutsideModulus p B)) : ResidueSpace p :=
  fun j => if hj : j∈B then z j else x ⟨j,hj⟩

lemma assembleOutside_freeze {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)]
    (B : Finset J) (z x : ResidueSpace p) :
    assembleOutside p B z (outsideCoordinate p B x)=freezeCoordinates B z x := by
  funext j
  simp only [assembleOutside,outsideCoordinate,freezeCoordinates]
  split_ifs <;> rfl

lemma frozenFourier_outside (F : ResidueSpace p → ℂ) (z : ResidueSpace p)
    (a : ResidueSpace (OutsideModulus p B)) :
    residueFourier p (fun x => F (freezeCoordinates B z x)) (outsideExtend p B a)=
      residueFourier (OutsideModulus p B) (fun x => F (assembleOutside p B z x)) a := by
  simp only [residueFourier,outsideExtend_char]
  rw [←expect_outside p B (fun x => F (assembleOutside p B z x)*conj (prodChar (OutsideModulus p B) a x))]
  simp only [assembleOutside_freeze]

lemma sequenceCoeff_outside (L : ℕ) (f : ℕ → ℝ) (a : ResidueSpace (OutsideModulus p B)) :
    sequenceCoeff p L f (outsideExtend p B a)=sequenceCoeff (OutsideModulus p B) L f a := by
  simp only [sequenceCoeff,outsideExtend_char]
  rfl

lemma actual_frozen_outside_coefficient (L Q H : ℕ) (f : ℕ → ℝ)
    (hHQ : H*(∏j∈B,p j)≤Q) (z : ResidueSpace p) (a : ResidueSpace (OutsideModulus p B))
    (ha : supportDenominator (OutsideModulus p B) a≤H) :
    residueFourier (OutsideModulus p B)
      (fun x => (actualTruncatedLift p L Q f (assembleOutside p B z x):ℂ)) a=
      sequenceCoeff (OutsideModulus p B) L (gatedSequence p B z f) a := by
  rw [←frozenFourier_outside p B (fun x => (actualTruncatedLift p L Q f x:ℂ)) z a, frozen_lift_fiber_fourier p L Q H f B hHQ z _
    (by rwa [outsideExtend_denominator]) (outsideExtend_disjoint p B a),sequenceCoeff_outside]

lemma outside_fiber_second_moment (F : ResidueSpace p → ℝ) (z : ResidueSpace p) :
    (𝔼 x,F (assembleOutside p B z x)^2)≤(∏j∈B,p j:ℝ)*(𝔼 x,F x^2) := by
  have h := expect_freeze_le (fun x => F x^2) (fun _ => sq_nonneg _) B z
  rw [←expect_outside p B (fun x => F (assembleOutside p B z x)^2)]
  simpa only [assembleOutside_freeze,ZMod.card] using h

end Outside

end SquareDifference.PairBridge

end

end OAI
