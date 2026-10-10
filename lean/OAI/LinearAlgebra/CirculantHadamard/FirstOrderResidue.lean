import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace OAI

universe uO uK uIota

/-!
# First-order residues of principal units

For a nonzero element `t` of a domain, a unit of the form `1 + t * a` has a
unique coefficient `a`. A ring homomorphism killing `t` sends the coefficient
of a product to the sum of the coefficients. This constructs the actual
first-order homomorphism without identifying any quotient rings.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {O : Type uO} [CommRing O]

/-- Units whose difference from one is a multiple of the specified element. -/
def principalUnits (t : O) : Subgroup Oˣ where
  carrier := {u | ∃ a : O, (u : O) = 1 + t * a}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro u v ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b + t * a * b, ?_⟩
    change (u : O) * (v : O) = _
    rw [ha, hb]
    ring
  inv_mem' := by
    rintro u ⟨a, ha⟩
    refine ⟨-a * (↑u⁻¹ : O), ?_⟩
    have h := u.mul_inv
    rw [ha] at h
    linear_combination h

@[simp]
theorem mem_principalUnits (t : O) (u : Oˣ) :
    u ∈ principalUnits t ↔ ∃ a : O, (u : O) = 1 + t * a :=
  Iff.rfl

/-- The coefficient of a principal unit. Its uniqueness is proved separately
using the domain assumption and `t ≠ 0`. -/
noncomputable def principalUnitCoeff (t : O) (u : principalUnits t) : O :=
  Classical.choose u.property

theorem principalUnitCoeff_spec (t : O) (u : principalUnits t) :
    ((u : Oˣ) : O) = 1 + t * principalUnitCoeff t u :=
  Classical.choose_spec u.property

section Domain

variable [IsDomain O]

theorem principalUnitCoeff_eq (t : O) (ht : t ≠ 0) (u : principalUnits t)
    {a : O} (ha : ((u : Oˣ) : O) = 1 + t * a) :
    principalUnitCoeff t u = a := by
  apply mul_left_cancel₀ ht
  exact add_left_cancel ((principalUnitCoeff_spec t u).symm.trans ha)

theorem principalUnitCoeff_mul (t : O) (ht : t ≠ 0)
    (u v : principalUnits t) :
    principalUnitCoeff t (u * v) =
      principalUnitCoeff t u + principalUnitCoeff t v +
        t * principalUnitCoeff t u * principalUnitCoeff t v := by
  apply principalUnitCoeff_eq t ht
  change ((u : Oˣ) : O) * ((v : Oˣ) : O) = _
  rw [principalUnitCoeff_spec, principalUnitCoeff_spec]
  ring

variable {K : Type uK} [Field K]

/-- The actual first-order homomorphism associated with a nonzero element
killed by the given residue map. `Multiplicative K` uses addition in `K`. -/
noncomputable def actualFirstOrder (φ : O →+* K) (t : O) (ht : t ≠ 0)
    (hφt : φ t = 0) : principalUnits t →* Multiplicative K where
  toFun u := Multiplicative.ofAdd (φ (principalUnitCoeff t u))
  map_one' := by
    apply Multiplicative.toAdd.injective
    change φ (principalUnitCoeff t 1) = 0
    rw [principalUnitCoeff_eq t ht 1 (a := 0) (by simp), map_zero]
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    change φ (principalUnitCoeff t (u * v)) =
      φ (principalUnitCoeff t u) + φ (principalUnitCoeff t v)
    rw [principalUnitCoeff_mul t ht]
    simp [hφt]

theorem actualFirstOrder_apply_of_eq (φ : O →+* K) (t : O) (ht : t ≠ 0)
    (hφt : φ t = 0) (u : principalUnits t) {a : O}
    (ha : ((u : Oˣ) : O) = 1 + t * a) :
    (actualFirstOrder φ t ht hφt u).toAdd = φ a := by
  change φ (principalUnitCoeff t u) = φ a
  rw [principalUnitCoeff_eq t ht u ha]

/-- An exact signed product identity among principal units gives a vanishing
sum of their first-order residues. Representations are required only on `s`. -/
theorem first_order_sum_eq_zero_of_prod_eq_one {ι : Type uIota}
    (φ : O →+* K) (t : O) (ht : t ≠ 0) (hφt : φ t = 0)
    (s : Finset ι) (u : ι → Oˣ) (L : ι → O) (ε : ι → ℤ)
    (hrep : ∀ i ∈ s, (u i : O) = 1 + t * L i)
    (hprod : (∏ i ∈ s, (u i) ^ (ε i)) = 1) :
    ∑ i ∈ s, (ε i : K) * φ (L i) = 0 := by
  classical
  let v : ι → principalUnits t := fun i =>
    if hi : i ∈ s then ⟨u i, ⟨L i, hrep i hi⟩⟩ else 1
  have hv (i : ι) (hi : i ∈ s) : (v i : Oˣ) = u i := by
    simp only [v, dite_eq_left hi]
  have hp : (∏ i ∈ s, (v i) ^ (ε i)) = 1 := by
    apply Subtype.ext
    change (principalUnits t).subtype (∏ i ∈ s, (v i) ^ (ε i)) =
      (principalUnits t).subtype 1
    rw [map_prod, map_one]
    calc
      (∏ i ∈ s, (principalUnits t).subtype ((v i) ^ (ε i))) =
          ∏ i ∈ s, (u i) ^ (ε i) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [map_zpow]
        change (v i : Oˣ) ^ (ε i) = (u i) ^ (ε i)
        rw [hv i hi]
      _ = 1 := hprod
  have hmap := congrArg
    (fun z : principalUnits t => (actualFirstOrder φ t ht hφt z).toAdd) hp
  have hsum :
      (∑ i ∈ s, (ε i) • (actualFirstOrder φ t ht hφt (v i)).toAdd) = 0 := by
    simpa only [map_prod, map_zpow, toAdd_prod,
      toAdd_zpow, map_one, toAdd_one] using hmap
  calc
    (∑ i ∈ s, (ε i : K) * φ (L i)) =
        ∑ i ∈ s, (ε i) • (actualFirstOrder φ t ht hφt (v i)).toAdd := by
      apply Finset.sum_congr rfl
      intro i hi
      have hvi : ((v i : Oˣ) : O) = 1 + t * L i := by
        rw [hv i hi]
        exact hrep i hi
      rw [actualFirstOrder_apply_of_eq φ t ht hφt (v i) hvi, zsmul_eq_mul]
    _ = 0 := hsum

end Domain

end CirculantHadamard

end OAI
