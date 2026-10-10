import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalAbelianRank
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.Group.Equiv.TypeTags

namespace OAI

/-! # Rational conjugation on an abelian normal subgroup

Conjugation extends to the rationalization. When the subgroup is torsion free,
the extended action has exactly the same kernel, namely its centralizer.
Together with the rank bound this is a finite-dimensional representation of
the centralizer quotient, without a finite-generation assumption on the
abelian subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative TensorProduct

variable {A : Type} [CommGroup A]

def rationalAbelianAut : MulAut A →*
    (RationalAbelianSpace A ≃ₗ[ℚ] RationalAbelianSpace A) where
  toFun e := e.toAdditive.toIntLinearEquiv.baseChange ℤ ℚ _ _
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    exact TensorProduct.AlgebraTensorModule.ext (fun _ _ => rfl)
  map_mul' e f := by
    apply LinearEquiv.toLinearMap_injective
    exact TensorProduct.AlgebraTensorModule.ext (fun _ _ => rfl)

@[simp]
theorem rationalAbelianAut_map (e : MulAut A) (a : Additive A) :
    rationalAbelianAut e (rationalAbelianMap a) =
      rationalAbelianMap (Additive.ofMul (e a.toMul)) := rfl

theorem rationalAbelianAut_injective (hA : HasNoNontrivialTorsion A) :
    Function.Injective (rationalAbelianAut (A := A)) := by
  intro e f hef
  ext a
  apply Additive.ofMul.injective
  apply rationalAbelianMap_injective hA
  exact congrArg (fun u => u (rationalAbelianMap (Additive.ofMul a))) hef

variable {G : Type} [Group G] (H : Subgroup G) [H.Normal] [IsMulCommutative H]

def rationalConjugation : G →*
    (RationalAbelianSpace H ≃ₗ[ℚ] RationalAbelianSpace H) :=
  rationalAbelianAut.comp (MulAut.conjNormal (H := H))

theorem rationalConjugation_ker (hH : HasNoNontrivialTorsion H) :
    (rationalConjugation H).ker = Subgroup.centralizer (H : Set G) := by
  ext g
  change rationalAbelianAut (A := H) (MulAut.conjNormal (H := H) g) =
    (1 : RationalAbelianSpace H ≃ₗ[ℚ] RationalAbelianSpace H) ↔ _
  rw [← (rationalAbelianAut (A := H)).map_one,
    (rationalAbelianAut_injective hH).eq_iff]
  constructor
  · intro hg a ha
    have he := congrArg (fun e : MulAut H => ((e ⟨a, ha⟩ : H) : G)) hg
    change g * a * g⁻¹ = a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hg
    ext a
    change g * (a : G) * g⁻¹ = a
    rw [← hg a a.property, mul_inv_cancel_right]

theorem rationalConjugation_ker_of_finiteDimension
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    (rationalConjugation H).ker = Subgroup.centralizer (H : Set G) :=
  rationalConjugation_ker H (hG.subgroup H).torsionFree

/-- The centralizer quotient acts faithfully on the rationalization. -/
def rationalConjugationQuotient (hH : HasNoNontrivialTorsion H) :
    (G ⧸ Subgroup.centralizer (H : Set G)) →*
      (RationalAbelianSpace H ≃ₗ[ℚ] RationalAbelianSpace H) :=
  QuotientGroup.lift _ (rationalConjugation H)
    (le_of_eq (rationalConjugation_ker H hH).symm)

theorem rationalConjugationQuotient_injective (hH : HasNoNontrivialTorsion H) :
    Function.Injective (rationalConjugationQuotient H hH) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (rationalConjugation_ker H hH).symm

end PolycyclicRecognition

end

end OAI
