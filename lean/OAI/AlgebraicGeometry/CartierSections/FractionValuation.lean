import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Basic.ENNReal.Basic

namespace OAI

/-!
# Extending finite valuations to a fraction field

A finite nonnegative valuation on a domain extends uniquely to its fraction
field with values in the extended real line.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal
namespace CartierSections

/-- ENNReal, used for nonnegative local-ring values, embedded in the extended
real additive group used on the fraction field. -/
def nonnegToExtendedReal : ENNReal →+ WithTop ℝ :=
  NNReal.toRealHom.toAddMonoidHom.withTopMap

@[simp] theorem nonnegToExtendedReal_top : nonnegToExtendedReal ⊤ = ⊤ := rfl
@[simp] theorem nonnegToExtendedReal_coe (a : NNReal) :
    nonnegToExtendedReal a = ((a : ℝ) : WithTop ℝ) := rfl

lemma nonnegToExtendedReal_monotone : Monotone nonnegToExtendedReal := by
  intro a b hab
  by_cases hb : b = ⊤
  · subst b; simp
  lift b to NNReal using hb with b
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hab
  lift a to NNReal using ha with a
  simpa using hab

@[simp] lemma nonnegToExtendedReal_eq_top {a : ENNReal} :
    nonnegToExtendedReal a = ⊤ ↔ a = ⊤ := by
  by_cases ha : a = ⊤
  · simp [ha]
  · lift a to NNReal using ha with a
    simp

section LocalValuation
variable {A : Type*} [CommRing A]

/-- Regard a nonnegative valuation as an extended-real valuation. -/
noncomputable def realLocalValuation (v : AddValuation A ENNReal) : AddValuation A (WithTop ℝ) :=
  v.map nonnegToExtendedReal nonnegToExtendedReal_top nonnegToExtendedReal_monotone

@[simp] lemma realLocalValuation_apply (v : AddValuation A ENNReal) (a : A) :
    realLocalValuation v a = nonnegToExtendedReal (v a) := rfl

end LocalValuation

section FractionField
variable {A K : Type*} [CommRing A] [IsDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]

lemma realLocalValuation_denominators (v : AddValuation A ENNReal)
    (hv : ∀ a ≠ 0, v a ≠ ⊤) :
    nonZeroDivisors A ≤ (AddValuation.toValuation (realLocalValuation v)).supp.primeCompl := by
  intro a ha
  change realLocalValuation v a ≠ ⊤
  simpa using hv a (mem_nonZeroDivisors_iff_ne_zero.mp ha)

/-- Extend a valuation that is finite on nonzero elements to the fraction field. -/
noncomputable def fractionValuation (v : AddValuation A ENNReal)
    (hv : ∀ a ≠ 0, v a ≠ ⊤) : AddValuation K (WithTop ℝ) :=
  AddValuation.ofValuation ((AddValuation.toValuation (realLocalValuation v)).extendToLocalization
    (realLocalValuation_denominators v hv) K)

@[simp] lemma fractionValuation_algebraMap (v : AddValuation A ENNReal)
    (hv : ∀ a ≠ 0, v a ≠ ⊤) (a : A) :
    fractionValuation (K := K) v hv (algebraMap A K a) = nonnegToExtendedReal (v a) := by
  exact Valuation.extendToLocalization_apply_map_apply
    (AddValuation.toValuation (realLocalValuation v))
    (realLocalValuation_denominators v hv) K a

lemma fractionValuation_ratio (v : AddValuation A ENNReal)
    (hv : ∀ a ≠ 0, v a ≠ ⊤) (a b : A) :
    fractionValuation (K := K) v hv (algebraMap A K a / algebraMap A K b) =
      nonnegToExtendedReal (v a) - nonnegToExtendedReal (v b) := by
  rw [AddValuation.map_div, fractionValuation_algebraMap, fractionValuation_algebraMap]

/-- The extension is unique as a valuation of the function field. -/
lemma fractionValuation_unique (v : AddValuation A ENNReal)
    (hv : ∀ a ≠ 0, v a ≠ ⊤) (u : AddValuation K (WithTop ℝ))
    (hu : ∀ a, u (algebraMap A K a) = nonnegToExtendedReal (v a)) :
    u = fractionValuation v hv := by
  apply DFunLike.ext
  intro x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  rw [u.map_div, hu, hu, fractionValuation_ratio]

end FractionField
end CartierSections

end

end OAI
