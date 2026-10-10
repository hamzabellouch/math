import OAI.NumberTheory.PiExponent.Jets.DVRBranchExpansion
import OAI.NumberTheory.PiExponent.Jets.DVRBranchOrder

namespace OAI

noncomputable section
namespace PiExponent.DVRBranch
open CurveLocalOrder

variable (C A : Type*) [Field C] [IsAlgClosed C] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra C A]
    [Algebra.IsIntegral C (IsLocalRing.ResidueField A)]

def residueCoefficientMap : A →ₐ[C] C where
  toRingHom := residueAugmentation C A
  commutes' := residueAugmentation_algebraMap C A

@[simp] theorem residueCoefficientMap_ker :
    RingHom.ker (residueCoefficientMap C A).toRingHom = IsLocalRing.maximalIdeal A := by
  ext a
  change (residueCoefficientEquiv C A).symm (IsLocalRing.residue A a) = 0 ↔
    a ∈ IsLocalRing.maximalIdeal A
  rw [map_eq_zero_iff _ (AlgEquiv.injective _)]
  exact IsLocalRing.residue_eq_zero_iff a

def uniformizer : A := Classical.choose (IsDiscreteValuationRing.exists_irreducible A)

theorem uniformizer_irreducible : Irreducible (uniformizer A) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible A)

theorem residueCoefficientMap_ker_span :
    RingHom.ker (residueCoefficientMap C A).toRingHom = Ideal.span {uniformizer A} := by
  rw [residueCoefficientMap_ker, (uniformizer_irreducible A).maximalIdeal_eq]

def expansion : A →ₐ[C] PowerSeries C :=
  DVRBranchExpansion.expansionHom (residueCoefficientMap C A) (uniformizer A)
    (uniformizer_irreducible A).ne_zero (residueCoefficientMap_ker_span C A)

@[simp] theorem expansion_uniformizer : expansion C A (uniformizer A) = PowerSeries.X :=
  DVRBranchExpansion.expansionHom_uniformizer _ _ _ _

theorem expansion_order (a : A) :
    PowerSeries.order (expansion C A a) = IsDiscreteValuationRing.addVal A a :=
  DVRBranchOrder.algHom_order_eq_addVal (expansion C A) (uniformizer A)
    (uniformizer_irreducible A) (expansion_uniformizer C A) a

theorem expansion_injective : Function.Injective (expansion C A) :=
  DVRBranchOrder.algHom_injective (expansion C A) (uniformizer A)
    (uniformizer_irreducible A) (expansion_uniformizer C A)

@[simp] theorem expansion_constantCoeff (a : A) :
    PowerSeries.constantCoeff (expansion C A a) = residueAugmentation C A a :=
  DVRBranchExpansion.constantCoeff_expansionHom _ _ _ _ a

theorem expansion_order_eq_length {a : A} (ha : a ≠ 0) :
    PowerSeries.order (expansion C A a) = Module.length A (A ⧸ Ideal.span {a}) :=
  DVRBranchOrder.order_eq_principal_colength (expansion C A).toRingHom (uniformizer A)
    (uniformizer_irreducible A) (expansion_uniformizer C A) ha

end PiExponent.DVRBranch

end

end OAI
