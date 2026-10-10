import Mathlib
import OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder

namespace OAI

noncomputable section
open scoped nonZeroDivisors
open PiExponent.WeightedCurveDegree PiExponent.CurveLocalOrder

namespace PiExponent.DVRValuationUnique

variable {A E : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field E] [Algebra A E] [IsFractionRing A E]

def localFieldUnit (a : A) (ha : a ≠ 0) : Eˣ :=
  Units.mk0 (algebraMap A E a) ((map_ne_zero_iff _ (IsFractionRing.injective A E)).mpr ha)

omit [IsDomain A] [IsDiscreteValuationRing A] in
@[simp] theorem localFieldUnit_val (a : A) (ha : a ≠ 0) :
    ((localFieldUnit (E := E) a ha : Eˣ) : E) = algebraMap A E a := rfl

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A E] in
theorem integerOrder_unit_eq_zero
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a)) (u : Aˣ) :
    integerOrder v (Units.map (algebraMap A E) u) = 0 := by
  have hpos : 0 ≤ integerOrder v (Units.map (algebraMap A E) u) := by
    apply WithTop.coe_le_coe.mp
    simpa using hregular (u : A)
  have hneg : 0 ≤ integerOrder v (Units.map (algebraMap A E) u⁻¹) := by
    apply WithTop.coe_le_coe.mp
    simpa using hregular (u⁻¹ : Aˣ)
  simp only [map_inv, integerOrder_inv] at hneg
  omega

theorem exists_order_eq_uniformizer_multiple
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a))
    {π : A} (hπ : Irreducible π) (a : A) (ha : a ≠ 0) :
    ∃ n : ℕ, integerOrder v (localFieldUnit (E := E) a ha) =
      (n : ℤ) * integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) ∧
      IsDiscreteValuationRing.addVal A a = n := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  refine ⟨n, ?_, IsDiscreteValuationRing.addVal_def' u hπ n⟩
  have he : localFieldUnit (E := E) ((u : A) * π ^ n) ha =
      Units.map (algebraMap A E) u * localFieldUnit (E := E) π hπ.ne_zero ^ n := by
    ext
    simp [localFieldUnit, map_mul, map_pow]
  rw [he, integerOrder_mul, integerOrder_pow, integerOrder_unit_eq_zero v hregular]
  simp

theorem uniformizer_order_dvd
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a))
    {π : A} (hπ : Irreducible π) (z : Eˣ) :
    integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) ∣ integerOrder v z := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A (z : E)
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha0 : a ≠ 0 := by
    intro ha
    apply z.ne_zero
    rw [← hab, ha, map_zero, zero_div]
  have hz : z = localFieldUnit (E := E) a ha0 / localFieldUnit (E := E) b hb0 := by
    ext
    simpa only [Units.val_div_eq_div_val, localFieldUnit_val] using hab.symm
  obtain ⟨m, hm, _⟩ := exists_order_eq_uniformizer_multiple v hregular hπ a ha0
  obtain ⟨n, hn, _⟩ := exists_order_eq_uniformizer_multiple v hregular hπ b hb0
  rw [hz, integerOrder_div, hm, hn]
  exact ⟨(m : ℤ) - n, by ring⟩

theorem eq_fractionAddValuation
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a))
    (hcenter : ∀ a ∈ IsLocalRing.maximalIdeal A, a ≠ 0 → 0 < v (algebraMap A E a))
    (hnormalized : ∃ z : Eˣ, integerOrder v z = 1) :
    v = fractionAddValuation A E := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπmem : π ∈ IsLocalRing.maximalIdeal A := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_singleton π)
  have hpos : 0 < integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) := by
    apply WithTop.coe_lt_coe.mp
    simpa using hcenter π hπmem hπ.ne_zero
  have hone : integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) = 1 := by
    obtain ⟨z, hz⟩ := hnormalized
    apply Int.eq_one_of_dvd_one hpos.le
    rw [← hz]
    exact uniformizer_order_dvd v hregular hπ z
  have hlocal (a : A) : v (algebraMap A E a) = localAddValuation A a := by
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨n, hn, hcanonical⟩ := exists_order_eq_uniformizer_multiple v hregular hπ a ha
    rw [hone, mul_one] at hn
    rw [localAddValuation_apply, hcanonical, enatToIntegerOrder_natCast]
    rw [← localFieldUnit_val a ha, ← coe_integerOrder, hn]
    rfl
  ext x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A x
  rw [AddValuation.map_div, AddValuation.map_div, hlocal, hlocal,
    fractionAddValuation_algebraMap, fractionAddValuation_algebraMap]

theorem fractionAddValuation_normalized :
    ∃ z : Eˣ, integerOrder (fractionAddValuation A E) z = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  refine ⟨localFieldUnit (E := E) π hπ.ne_zero, ?_⟩
  apply WithTop.coe_injective
  rw [coe_integerOrder, localFieldUnit_val, fractionAddValuation_algebraMap,
    localAddValuation_apply, IsDiscreteValuationRing.addVal_uniformizer hπ]
  rfl

end PiExponent.DVRValuationUnique

end

end OAI
