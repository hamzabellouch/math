import Mathlib
import OAI.NumberTheory.PiExponent.Geometry.CurveValuationCenter

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveProductFormula
open PiExponent.CurveZeroPole PiExponent.CurveValuationCenter
open PiExponent.WeightedCurveDegree

def placeOrder {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) : ℤ := integerOrder p.valuation z

@[simp] theorem placeOrder_inv {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) : placeOrder p z⁻¹ = -placeOrder p z := by
  exact integerOrder_inv p.valuation z

theorem valuation_pos_iff_order_pos {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) : 0 < p.valuation (z : E) ↔ 0 < placeOrder p z := by
  rw [← coe_integerOrder]
  exact WithTop.coe_lt_coe

theorem order_ne_zero_iff_positive_or_inverse
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) :
    placeOrder p z ≠ 0 ↔ 0 < p.valuation (z : E) ∨ 0 < p.valuation ((z : E)⁻¹) := by
  rw [valuation_pos_iff_order_pos p z]
  rw [← Units.val_inv_eq_inv_val]
  rw [valuation_pos_iff_order_pos, placeOrder_inv]
  omega

def positivePlaces {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] : Finset (NormalizedPlace F E) :=
  (finite_positivePlaces f hf).toFinset

@[simp] theorem mem_positivePlaces
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] (p : NormalizedPlace F E) :
    p ∈ positivePlaces f hf ↔ 0 < p.valuation f := by
  classical
  exact (finite_positivePlaces f hf).mem_toFinset

abbrev positivePlacesFintype
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    Fintype {p : NormalizedPlace F E // 0 < p.valuation f} :=
  let := parameterZeroPlacesFintype f hf
  Fintype.ofEquiv (parameterZeroPlaces f hf) (positivePlaceEquivZeroPlaces f hf).symm

theorem sum_positiveOrders_eq
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    ∑ p ∈ positivePlaces f hf, placeOrder p (Units.mk0 f hf.ne_zero) = parameterZeroOrder f hf := by
  let := positivePlacesFintype f hf
  let := parameterZeroPlacesFintype f hf
  rw [Finset.sum_subtype (positivePlaces f hf) (mem_positivePlaces f hf)]
  calc
    _ = ∑ q : parameterZeroPlaces f hf,
        placeOrder (parameterNormalizedPlace f hf q) (Units.mk0 f hf.ne_zero) :=
      ((positivePlaceEquivZeroPlaces f hf).symm.sum_comp
        (fun p => placeOrder p.1 (Units.mk0 f hf.ne_zero))).symm
    _ = _ := (parameterZeroOrder_eq_sum f hf).symm

theorem finite_support_placeOrder
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    (Function.support (fun p : NormalizedPlace F E => placeOrder p (Units.mk0 f hf.ne_zero))).Finite := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  apply ((finite_positivePlaces f hf).union
    (finite_positivePlaces f⁻¹ (transcendental_inverse f hf))).subset
  intro p hp
  exact (order_ne_zero_iff_positive_or_inverse p (Units.mk0 f hf.ne_zero)).mp hp

def principalDivisor
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] : NormalizedPlace F E →₀ ℤ :=
  Finsupp.ofSupportFinite (fun p => placeOrder p (Units.mk0 f hf.ne_zero))
    (finite_support_placeOrder f hf)

@[simp] theorem principalDivisor_apply
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] (p : NormalizedPlace F E) :
    principalDivisor f hf p = placeOrder p (Units.mk0 f hf.ne_zero) := rfl

theorem principalDivisor_degree_zero
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    (principalDivisor f hf).sum (fun _ n => n) = 0 := by
  classical
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let z : Eˣ := Units.mk0 f hf.ne_zero
  let zi : Eˣ := Units.mk0 f⁻¹ (transcendental_inverse f hf).ne_zero
  have hiz : zi = z⁻¹ := by ext; simp [zi, z]
  have hsup : (principalDivisor f hf).support ⊆
      positivePlaces f hf ∪ positivePlaces f⁻¹ (transcendental_inverse f hf) := by
    intro p hp
    have hn : placeOrder p z ≠ 0 := by simpa [z] using Finsupp.mem_support_iff.mp hp
    simpa only [Finset.mem_union, mem_positivePlaces, z, Units.val_mk0] using
      (order_ne_zero_iff_positive_or_inverse p z).mp hn
  have hdisj : Disjoint (positivePlaces f hf)
      (positivePlaces f⁻¹ (transcendental_inverse f hf)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hi
    have hp' : 0 < placeOrder p z :=
      (valuation_pos_iff_order_pos p z).mp ((mem_positivePlaces f hf p).mp hp)
    have hi' : 0 < placeOrder p zi :=
      (valuation_pos_iff_order_pos p zi).mp
        ((mem_positivePlaces f⁻¹ (transcendental_inverse f hf) p).mp hi)
    rw [hiz, placeOrder_inv] at hi'
    omega
  rw [Finsupp.sum_of_support_subset _ hsup _ (by intro _ _; rfl)]
  simp only [principalDivisor_apply]
  rw [Finset.sum_union hdisj, sum_positiveOrders_eq]
  have hi : (∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), placeOrder p z) =
      -parameterZeroOrder f⁻¹ (transcendental_inverse f hf) := by
    calc
      _ = ∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), -(placeOrder p zi) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [hiz, placeOrder_inv, neg_neg]
      _ = -(∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), placeOrder p zi) :=
        Finset.sum_neg_distrib (fun p => placeOrder p zi)
      _ = _ := congrArg Neg.neg (sum_positiveOrders_eq f⁻¹ (transcendental_inverse f hf))
  change parameterZeroOrder f hf + (∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf),
    placeOrder p z) = 0
  rw [hi, zero_pole_order_eq]
  exact add_neg_cancel _

theorem valuation_constant_eq_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (c : F) (hc : c ≠ 0) :
    p.valuation (algebraMap F E c) = 0 := by
  let z : Eˣ := Units.mk0 (algebraMap F E c) ((map_ne_zero_iff _ (algebraMap F E).injective).mpr hc)
  have hpos : 0 ≤ integerOrder p.valuation z := by
    apply WithTop.coe_le_coe.mp
    rw [coe_integerOrder]
    exact p.constants_nonneg c
  have hinv : 0 ≤ integerOrder p.valuation z⁻¹ := by
    apply WithTop.coe_le_coe.mp
    rw [coe_integerOrder]
    simpa [z] using p.constants_nonneg c⁻¹
  rw [integerOrder_inv] at hinv
  have hz : integerOrder p.valuation z = 0 := by omega
  have he := coe_integerOrder p.valuation z
  rw [hz] at he
  exact he.symm

theorem placeOrder_constant_eq_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (c : F) (hc : c ≠ 0) :
    placeOrder p (Units.mk0 (algebraMap F E c) ((map_ne_zero_iff _ (algebraMap F E).injective).mpr hc)) = 0 := by
  apply WithTop.coe_injective
  rw [placeOrder, coe_integerOrder]
  exact valuation_constant_eq_zero p c hc

end PiExponent.CurveProductFormula

end

end OAI
