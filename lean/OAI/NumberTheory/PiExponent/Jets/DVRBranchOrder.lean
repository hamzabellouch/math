import OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder

namespace OAI

noncomputable section
namespace PiExponent.DVRBranchOrder

variable {A C : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field C]

theorem order_eq_addVal (φ : A →+* PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) (a : A) :
    PowerSeries.order (φ a) = IsDiscreteValuationRing.addVal A a := by
  by_cases ha : a = 0
  · subst a
    rw [map_zero, PowerSeries.order_zero, IsDiscreteValuationRing.addVal_zero]
  · obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [map_mul, map_pow, hφπ, PowerSeries.order_mul, PowerSeries.order_X_pow,
      PowerSeries.order_zero_of_isUnit (u.isUnit.map φ), zero_add,
      IsDiscreteValuationRing.addVal_def' u hπ]

theorem injective (φ : A →+* PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) : Function.Injective φ := by
  intro a b hab
  have hz : φ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have ho := order_eq_addVal φ π hπ hφπ (a - b)
  rw [hz, PowerSeries.order_zero] at ho
  exact sub_eq_zero.mp (IsDiscreteValuationRing.addVal_eq_top_iff.mp ho.symm)

theorem order_eq_top_iff (φ : A →+* PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) (a : A) :
    PowerSeries.order (φ a) = ⊤ ↔ a = 0 := by
  rw [order_eq_addVal φ π hπ hφπ, IsDiscreteValuationRing.addVal_eq_top_iff]

theorem order_eq_zero_iff_isUnit (φ : A →+* PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) (a : A) :
    PowerSeries.order (φ a) = 0 ↔ IsUnit a := by
  rw [order_eq_addVal φ π hπ hφπ, IsDiscreteValuationRing.addVal_eq_zero_iff]

theorem order_le_iff_dvd (φ : A →+* PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) (a b : A) :
    PowerSeries.order (φ a) ≤ PowerSeries.order (φ b) ↔ a ∣ b := by
  rw [order_eq_addVal φ π hπ hφπ, order_eq_addVal φ π hπ hφπ,
    IsDiscreteValuationRing.addVal_le_iff_dvd]

theorem order_eq_principal_colength (φ : A →+* PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) {a : A} (ha : a ≠ 0) :
    PowerSeries.order (φ a) = Module.length A (A ⧸ Ideal.span {a}) := by
  rw [order_eq_addVal φ π hπ hφπ, CurveLocalOrder.length_quotient_span_eq_addVal ha]

theorem fraction_order_eq_branch_order {E : Type*} [Field E] [Algebra A E] [IsFractionRing A E]
    (φ : A →+* PowerSeries C) (π : A) (hπ : Irreducible π)
    (hφπ : φ π = PowerSeries.X) (a : A) :
    CurveLocalOrder.fractionAddValuation A E (algebraMap A E a) =
      CurveLocalOrder.enatToIntegerOrder (PowerSeries.order (φ a)) := by
  rw [CurveLocalOrder.fractionAddValuation_algebraMap, CurveLocalOrder.localAddValuation_apply,
    order_eq_addVal φ π hπ hφπ]

theorem integerOrder_eq_branch_order {E : Type*} [Field E] [Algebra A E] [IsFractionRing A E]
    (φ : A →+* PowerSeries C) (π : A) (hπ : Irreducible π)
    (hφπ : φ π = PowerSeries.X) {a : A} (ha : a ≠ 0) :
    WeightedCurveDegree.integerOrder (CurveLocalOrder.fractionAddValuation A E)
      (Units.mk0 (algebraMap A E a) ((map_ne_zero_iff _ (IsFractionRing.injective A E)).mpr ha)) =
        ((PowerSeries.order (φ a)).toNat : ℤ) := by
  rw [CurveLocalOrder.integerOrder_field_image_eq_length ha,
    ← order_eq_principal_colength φ π hπ hφπ ha]

variable [Algebra C A]

theorem algHom_order_eq_addVal (φ : A →ₐ[C] PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) (a : A) :
    PowerSeries.order (φ a) = IsDiscreteValuationRing.addVal A a :=
  order_eq_addVal φ.toRingHom π hπ hφπ a

theorem algHom_injective (φ : A →ₐ[C] PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) : Function.Injective φ :=
  injective φ.toRingHom π hπ hφπ

end PiExponent.DVRBranchOrder
end

end OAI
