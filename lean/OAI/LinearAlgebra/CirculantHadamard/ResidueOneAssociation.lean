import Mathlib.Algebra.Regular.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

namespace OAI

universe uS uk

/-!
# Association by a unit with residue one

This algebraic relation expresses the local comparison conclusion without
introducing division in the coefficient ring. The scalar-cancellation lemmas
require regularity explicitly; they do not give group rings a domain instance.
For a local ring, the residue map is the quotient by its maximal ideal.
-/

namespace CirculantHadamard.LocalComparison

variable {S : Type uS} {k : Type uk} [CommRing S] [CommRing k]

/-- `x` differs from `y` by multiplication by a unit whose residue is one. -/
def ResidueOneAssociated (residue : S →+* k) (x y : S) : Prop :=
  ∃ u : Sˣ, x = (u : S) * y ∧ residue (u : S) = 1

theorem residue_inv_eq_one (residue : S →+* k) {u : Sˣ}
    (hu : residue (u : S) = 1) : residue (↑u⁻¹ : S) = 1 := by
  have h : residue (u : S) * residue (↑u⁻¹ : S) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  simpa only [hu, one_mul] using h

namespace ResidueOneAssociated

variable {residue : S →+* k} {x y z c x' y' : S}

@[refl] theorem refl (residue : S →+* k) (x : S) :
    ResidueOneAssociated residue x x := by
  exact ⟨1, by simp, by simp⟩

@[symm] theorem symm (h : ResidueOneAssociated residue x y) :
    ResidueOneAssociated residue y x := by
  obtain ⟨u, hxy, hu⟩ := h
  refine ⟨u⁻¹, ?_, residue_inv_eq_one residue hu⟩
  rw [hxy, Units.inv_mul_cancel_left]

@[trans] theorem trans (hxy : ResidueOneAssociated residue x y)
    (hyz : ResidueOneAssociated residue y z) : ResidueOneAssociated residue x z := by
  obtain ⟨u, hxy, hu⟩ := hxy
  obtain ⟨v, hyz, hv⟩ := hyz
  refine ⟨u * v, ?_, ?_⟩
  · simp only [Units.val_mul, hxy, hyz, mul_assoc]
  · simp only [Units.val_mul, map_mul, hu, hv, one_mul]

theorem residue_eq (h : ResidueOneAssociated residue x y) : residue x = residue y := by
  obtain ⟨u, hxy, hu⟩ := h
  rw [hxy, map_mul, hu, one_mul]

theorem mul_left (h : ResidueOneAssociated residue x y) (c : S) :
    ResidueOneAssociated residue (c * x) (c * y) := by
  obtain ⟨u, hxy, hu⟩ := h
  refine ⟨u, ?_, hu⟩
  rw [hxy]
  ac_rfl

/-- A common regular scalar can be cancelled even if the ambient ring has
zero divisors. This is the form used when comparing scalar-divided factors. -/
theorem mul_left_iff (residue : S →+* k) (hc : IsLeftRegular c) :
    ResidueOneAssociated residue (c * x) (c * y) ↔
      ResidueOneAssociated residue x y := by
  constructor
  · rintro ⟨u, hxy, hu⟩
    refine ⟨u, hc ?_, hu⟩
    calc
      c * x = (u : S) * (c * y) := hxy
      _ = c * ((u : S) * y) := by ac_rfl
  · exact fun h => h.mul_left c

theorem mul (h : ResidueOneAssociated residue x y)
    (h' : ResidueOneAssociated residue x' y') :
    ResidueOneAssociated residue (x * x') (y * y') := by
  obtain ⟨u, hxy, hu⟩ := h
  obtain ⟨v, hxy', hv⟩ := h'
  refine ⟨u * v, ?_, ?_⟩
  · rw [hxy, hxy', Units.val_mul]
    ac_rfl
  · simp only [Units.val_mul, map_mul, hu, hv, one_mul]

/-- With equal nonzero products, a comparison for one factor gives the inverse
unit as comparison for the other factor. Only regularity of `y` is needed. -/
theorem product_complement_of_regular (h : ResidueOneAssociated residue x y)
    (hprod : x * x' = y * y') (hy : IsLeftRegular y) :
    ResidueOneAssociated residue x' y' := by
  obtain ⟨u, hxy, hu⟩ := h
  have hcancel : (u : S) * x' = y' := by
    apply hy
    calc
      y * ((u : S) * x') = ((u : S) * y) * x' := by ac_rfl
      _ = x * x' := by rw [← hxy]
      _ = y * y' := hprod
  refine ⟨u⁻¹, ?_, residue_inv_eq_one residue hu⟩
  rw [← hcancel, Units.inv_mul_cancel_left]

/-- The two-factor step used in the character-comparison base case. -/
theorem product_complement [IsDomain S] (h : ResidueOneAssociated residue x y)
    (hprod : x * x' = y * y') (hne : y * y' ≠ 0) :
    ResidueOneAssociated residue x' y' := by
  have hy : y ≠ 0 := fun hz => hne (by rw [hz, zero_mul])
  exact h.product_complement_of_regular hprod (fun _ _ h => mul_left_cancel₀ hy h)

theorem mul_left_iff_of_ne_zero [IsDomain S] (residue : S →+* k) (hc : c ≠ 0) :
    ResidueOneAssociated residue (c * x) (c * y) ↔
      ResidueOneAssociated residue x y :=
  mul_left_iff residue (fun _ _ h => mul_left_cancel₀ hc h)

/-- Two units with the same residue differ by a unit with residue one. -/
theorem of_isUnit_of_residue_eq (residue : S →+* k)
    (hx : IsUnit x) (hy : IsUnit y) (hres : residue x = residue y) :
    ResidueOneAssociated residue x y := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  refine ⟨u * v⁻¹, ?_, ?_⟩
  · simp only [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  · rw [Units.val_mul, map_mul, hres, ← map_mul, Units.mul_inv, map_one]

end ResidueOneAssociated

section ActualResidueField

variable [IsLocalRing S] {x y : S}

/-- Equality to the residue of a unit forces an element of a local ring to be
a unit. The residue map is the actual quotient by the maximal ideal. -/
theorem isUnit_of_residue_eq (hy : IsUnit y)
    (hres : IsLocalRing.residue S x = IsLocalRing.residue S y) : IsUnit x := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit x).mp
  rw [hres]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit y).mpr hy

/-- Concrete local-ring base case: an augmentation unit and agreement in the
residue field suffice to construct the comparison unit. -/
theorem residueOneAssociated_of_isUnit_residue_eq (hy : IsUnit y)
    (hres : IsLocalRing.residue S x = IsLocalRing.residue S y) :
    ResidueOneAssociated (IsLocalRing.residue S) x y :=
  ResidueOneAssociated.of_isUnit_of_residue_eq (IsLocalRing.residue S)
    (isUnit_of_residue_eq hy hres) hy hres

end ActualResidueField

end CirculantHadamard.LocalComparison

end OAI
