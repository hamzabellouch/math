import Mathlib

namespace OAI

noncomputable section

namespace Kervaire

universe u

abbrev WordGroup (A : Type u) [Group A] := Monoid.Coprod A (Multiplicative ℤ)

def exponentSum {A : Type u} [Group A] (w : WordGroup A) : ℤ :=
  Multiplicative.toAdd (Monoid.Coprod.snd w)

def Unimodular {A : Type u} [Group A] (w : WordGroup A) : Prop :=
  exponentSum w = 1 ∨ exponentSum w = -1

def relatorClosure {A : Type u} [Group A] (w : WordGroup A) : Subgroup (WordGroup A) :=
  Subgroup.normalClosure ({w} : Set (WordGroup A))

instance {A : Type u} [Group A] (w : WordGroup A) : (relatorClosure w).Normal :=
  inferInstanceAs (Subgroup.normalClosure ({w} : Set (WordGroup A))).Normal

abbrev RelatorQuotient {A : Type u} [Group A] (w : WordGroup A) :=
  WordGroup A ⧸ relatorClosure w

def coefficientMap {A : Type u} [Group A] (w : WordGroup A) : A →* RelatorQuotient w :=
  (QuotientGroup.mk' (relatorClosure w)).comp Monoid.Coprod.inl

theorem coefficient_injective (A : Type u) [Group A] (w : WordGroup A)
    (hw : Unimodular w) : Function.Injective (coefficientMap w) := by
  sorry

end Kervaire

end

end OAI
