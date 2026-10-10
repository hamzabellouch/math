import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Localization

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W09

variable (K : Type*) [Field K] (α β : Type*)

abbrev SplitPolynomial := MvPolynomial (α ⊕ β) K
abbrev CoefficientPolynomial := MvPolynomial β K
abbrev CoefficientFractionField := FractionRing (CoefficientPolynomial K β)
abbrev FractionCoefficientPolynomial := MvPolynomial α (CoefficientFractionField K β)

def coefficientDenominators : Submonoid (SplitPolynomial K α β) :=
  (nonZeroDivisors (CoefficientPolynomial K β)).map
    (MvPolynomial.rename (Sum.inr : β → α ⊕ β)).toRingHom

abbrev PolynomialCoefficientLocalization := Localization (coefficientDenominators K α β)

theorem coefficientRename_injective :
    Function.Injective (MvPolynomial.rename (Sum.inr : β → α ⊕ β) :
      CoefficientPolynomial K β → SplitPolynomial K α β) :=
  MvPolynomial.rename_injective _ Sum.inr_injective

@[simp] theorem mem_coefficientDenominators (p : SplitPolynomial K α β) :
    p ∈ coefficientDenominators K α β ↔
      ∃ f : CoefficientPolynomial K β, f ≠ 0 ∧ MvPolynomial.rename Sum.inr f = p := by
  simp [coefficientDenominators, Submonoid.mem_map, mem_nonZeroDivisors_iff_ne_zero]

@[simp] theorem sumAlgEquiv_coefficientRename (f : CoefficientPolynomial K β) :
    MvPolynomial.sumAlgEquiv K α β (MvPolynomial.rename Sum.inr f) = MvPolynomial.C f := by
  exact congrArg (fun g : CoefficientPolynomial K β →ₐ[K]
      MvPolynomial α (CoefficientPolynomial K β) => g f)
    (MvPolynomial.sumAlgEquiv_comp_rename_inr K α β)

theorem sumAlgEquiv_coefficientDenominators :
    (coefficientDenominators K α β).map (MvPolynomial.sumAlgEquiv K α β) =
      (nonZeroDivisors (CoefficientPolynomial K β)).map (MvPolynomial.C (σ := α)) := by
  ext y
  constructor
  · rintro ⟨x, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, hf, (sumAlgEquiv_coefficientRename K α β f).symm⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨MvPolynomial.rename Sum.inr f, ⟨f, hf, rfl⟩,
      sumAlgEquiv_coefficientRename K α β f⟩

attribute [local instance] MvPolynomial.algebraMvPolynomial

local instance coefficientPolynomial_scalarTower :
    IsScalarTower K (MvPolynomial α (CoefficientPolynomial K β))
      (FractionCoefficientPolynomial K α β) :=
  IsScalarTower.of_algebraMap_eq (fun c => by
    change MvPolynomial.C (algebraMap K (CoefficientFractionField K β) c) =
      MvPolynomial.map
        (algebraMap (CoefficientPolynomial K β) (CoefficientFractionField K β))
        (MvPolynomial.C (MvPolynomial.C c))
    rw [MvPolynomial.map_C]
    exact congrArg (MvPolynomial.C (σ := α))
      (IsScalarTower.algebraMap_apply K (CoefficientPolynomial K β)
        (CoefficientFractionField K β) c))

def polynomialCoefficientLocalizationEquiv :
    PolynomialCoefficientLocalization K α β ≃ₐ[K] FractionCoefficientPolynomial K α β :=
  IsLocalization.algEquivOfAlgEquiv
    (PolynomialCoefficientLocalization K α β) (FractionCoefficientPolynomial K α β)
    (MvPolynomial.sumAlgEquiv K α β) (sumAlgEquiv_coefficientDenominators K α β)

@[simp] theorem polynomialCoefficientLocalizationEquiv_algebraMap
    (p : SplitPolynomial K α β) :
    polynomialCoefficientLocalizationEquiv K α β
      (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β) p) =
      MvPolynomial.map
        (algebraMap (CoefficientPolynomial K β) (CoefficientFractionField K β))
        (MvPolynomial.sumAlgEquiv K α β p) :=
  IsLocalization.algEquivOfAlgEquiv_eq (sumAlgEquiv_coefficientDenominators K α β) p

@[simp] theorem polynomialCoefficientLocalizationEquiv_X_inl (i : α) :
    polynomialCoefficientLocalizationEquiv K α β
      (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β)
        (MvPolynomial.X (Sum.inl i))) = MvPolynomial.X i := by
  rw [polynomialCoefficientLocalizationEquiv_algebraMap]
  rw [MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.map_X]

@[simp] theorem polynomialCoefficientLocalizationEquiv_X_inr (j : β) :
    polynomialCoefficientLocalizationEquiv K α β
      (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β)
        (MvPolynomial.X (Sum.inr j))) =
      MvPolynomial.C (algebraMap (CoefficientPolynomial K β) (CoefficientFractionField K β)
        (MvPolynomial.X j)) := by
  rw [polynomialCoefficientLocalizationEquiv_algebraMap]
  rw [MvPolynomial.sumAlgEquiv_X_inr, MvPolynomial.map_C]

@[simp] theorem polynomialCoefficientLocalizationEquiv_coefficient
    (f : CoefficientPolynomial K β) :
    polynomialCoefficientLocalizationEquiv K α β
      (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β)
        (MvPolynomial.rename Sum.inr f)) =
      MvPolynomial.C (algebraMap (CoefficientPolynomial K β) (CoefficientFractionField K β) f) := by
  rw [polynomialCoefficientLocalizationEquiv_algebraMap,
    sumAlgEquiv_coefficientRename, MvPolynomial.map_C]

theorem polynomialCoefficientLocalizationEquiv_mk'
    (p : SplitPolynomial K α β) (s : coefficientDenominators K α β) :
    polynomialCoefficientLocalizationEquiv K α β
      (IsLocalization.mk' (PolynomialCoefficientLocalization K α β) p s) =
      IsLocalization.mk' (FractionCoefficientPolynomial K α β)
        (MvPolynomial.sumAlgEquiv K α β p)
        ⟨MvPolynomial.sumAlgEquiv K α β s,
          (sumAlgEquiv_coefficientDenominators K α β) ▸
            Submonoid.mem_map_of_mem (MvPolynomial.sumAlgEquiv K α β) s.property⟩ :=
  IsLocalization.algEquivOfAlgEquiv_mk' (sumAlgEquiv_coefficientDenominators K α β) p s

theorem coefficientDenominator_isUnit (f : CoefficientPolynomial K β) (hf : f ≠ 0) :
    IsUnit (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β)
      (MvPolynomial.rename Sum.inr f)) := by
  exact IsLocalization.map_units (PolynomialCoefficientLocalization K α β)
    ⟨MvPolynomial.rename Sum.inr f, (mem_coefficientDenominators K α β _).mpr ⟨f, hf, rfl⟩⟩

end PiExponentSiegelAux.W09

end

end OAI
