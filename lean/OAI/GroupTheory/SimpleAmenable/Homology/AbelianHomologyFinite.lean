import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.FullH2
import OAI.GroupTheory.SimpleAmenable.Simplicial.TranslationCoinvariants

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits
namespace AbelianHomologyFinite
open FreeChains SimpleAmenable

attribute [local instance 1200] Rep.hV2
variable (G:Type) [CommGroup G]
lemma fg [Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) 1)] : Group.FG G := by
  have :=TrivialHomology.abelianization_fg G
  exact Group.fg_of_surjective (f:=(Abelianization.equivOfComm (H:=G)).symm.toMonoidHom)
    (Abelianization.equivOfComm (H:=G)).symm.surjective
lemma finite (n:ℕ) [Group.FG G] : Module.Finite ℤ (groupHomology (Rep.trivial ℤ G ℤ) n) := by
  have : Algebra.FiniteType ℤ (MonoidAlgebra ℤ G) := MonoidAlgebra.finiteType_iff_group_fg.mpr inferInstance
  have : IsNoetherianRing (MonoidAlgebra ℤ G) := Algebra.FiniteType.isNoetherianRing ℤ _
  have : Module.Finite ℤ (Rep.trivial ℤ G ℤ).ρ.asModule := by
    exact Module.Finite.equiv (Representation.trivial ℤ G ℤ).asModuleEquiv.symm
  have : Module.Finite (MonoidAlgebra ℤ G) (Rep.trivial ℤ G ℤ).ρ.asModule :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  exact RingCoinvariants.finite_groupHomology _ n
end AbelianHomologyFinite
namespace TranslationNerve
open FreeChains

attribute [local instance 1200] Rep.hV2
variable (P:Type) [CommMonoid P]
lemma homology_finite_of_one (n:ℕ) [Module.Finite ℤ ((nerve (SingleObj P)).homology Z 1 : A)] :
    Module.Finite ℤ ((nerve (SingleObj P)).homology Z n : A) := by
  have : Module.Finite ℤ (groupHomology (Rep.trivial ℤ (TranslationFiltered.Q P) ℤ) 1) :=
    Module.Finite.equiv (completionHomologyIso P 1).toLinearEquiv
  have :=AbelianHomologyFinite.fg (TranslationFiltered.Q P)
  have :=AbelianHomologyFinite.finite (TranslationFiltered.Q P) n
  exact Module.Finite.equiv (completionHomologyIso P n).symm.toLinearEquiv
end TranslationNerve

end

end OAI
