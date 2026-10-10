import OAI.NumberTheory.Ostmann.Characters.TemplateCompositePivotSupportFamilyActual
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingFinite
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemoval

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTelescoping
open SymbolicHistory TemplateSupportRemoval
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [DecidableEq ι]

def familyCoprime (D : ι→Finset (Expr ι)) (i : ι) (a : ι→ℤ) : Prop :=
  ∀q∈D i,IsCoprime (a i) (q.integerEval a)

def familyPolynomial (D : ι→Finset (Expr ι)) (i : ι) : Prop :=
  ∀q∈D i,eraseCoordinate i q.numerator≠0

theorem hybridValue_eq_family (D : ι→Finset (Expr ι)) (removed : Finset ι)
    (i : ι) (hi : i∉removed) (core : (ι→ℤ)→Prop) (f : (ι→ℤ)→ℂ)
    (a : ι→ℤ) (p : ℕ) (ha : a i=(p:ℤ)) :
    hybridValue removed core (familyCoprime D) (familyPolynomial D) f a=
      familyCoprimeSupportedValue (D i)
        (decide (remainder removed i core (familyCoprime D) (familyPolynomial D) a))
        p (fun q=>q.integerEval a) (f a) := by
  rw [hybridValue,hybridSupport_iff_remainder removed i hi]
  unfold familyCoprimeSupportedValue
  have hc : (∀q∈D i,IsCoprime (p:ℤ) (q.integerEval a)) = familyCoprime D i a := by
    simp only [familyCoprime,ha]
  simp only [hc]
  by_cases hr : remainder removed i core (familyCoprime D) (familyPolynomial D) a <;>
    simp [hr]

theorem hybridValue_insert_eq_family (D : ι→Finset (Expr ι)) (removed : Finset ι)
    (i : ι) (hi : i∉removed) (core : (ι→ℤ)→Prop) (f : (ι→ℤ)→ℂ) (a : ι→ℤ) :
    hybridValue (insert i removed) core (familyCoprime D) (familyPolynomial D) f a=
      familyPolynomialEnlargedValue (D i) (fun q=>eraseCoordinate i q.numerator)
        (decide (remainder removed i core (familyCoprime D) (familyPolynomial D) a)) (f a) := by
  rw [hybridValue,hybridSupport_insert_iff removed i hi]
  have he : (∀q∈D i,eraseCoordinate i q.numerator≠0) = familyPolynomial D i := rfl
  simp only [familyPolynomialEnlargedValue,he]
  by_cases hr : remainder removed i core (familyCoprime D) (familyPolynomial D) a <;>
    by_cases hp : familyPolynomial D i <;> simp [hr,hp]

@[simp] theorem hybridValue_empty (D : ι→Finset (Expr ι)) (core : (ι→ℤ)→Prop)
    (f : (ι→ℤ)→ℂ) (a : ι→ℤ) :
    hybridValue ∅ core (familyCoprime D) (familyPolynomial D) f a=
      if core a ∧ ∀i,∀q∈D i,IsCoprime (a i) (q.integerEval a) then f a else 0 := by
  simp only [hybridValue,hybridSupport,Finset.notMem_empty,ite_false,familyCoprime]

@[simp] theorem hybridValue_univ [Fintype ι] (D : ι→Finset (Expr ι)) (core : (ι→ℤ)→Prop)
    (f : (ι→ℤ)→ℂ) (a : ι→ℤ) :
    hybridValue Finset.univ core (familyCoprime D) (familyPolynomial D) f a=
      if core a ∧ ∀i,∀q∈D i,eraseCoordinate i q.numerator≠0 then f a else 0 := by
  simp only [hybridValue,hybridSupport,Finset.mem_univ,ite_true,familyPolynomial]

end Ostmann.Characters.TemplateOneSidedSupportTelescoping

end

end OAI
