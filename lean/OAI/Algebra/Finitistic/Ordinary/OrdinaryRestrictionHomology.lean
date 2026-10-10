import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.QuasiIso

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.RestrictionHomology
universe u v
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

theorem mapsExact (K : ShortComplex (ModuleCat.{u} S)) (hK : K.Exact) :
    (K.map (ModuleCat.restrictScalars f)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff] at hK ⊢
  exact hK

theorem preservesHomology : (ModuleCat.restrictScalars.{u} f).PreservesHomology :=
  CategoryTheory.Functor.preservesHomology_of_map_exact _ (mapsExact f)

theorem quasiIso_iff {I : Type v} {c : ComplexShape I}
    {K L : HomologicalComplex (ModuleCat.{u} S) c} (g : K ⟶ L) :
    QuasiIso (((ModuleCat.restrictScalars f).mapHomologicalComplex c).map g) ↔ QuasiIso g := by
  let := preservesHomology f
  exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology g (ModuleCat.restrictScalars f)
end LittleFinitistic.RestrictionHomology

end

end OAI
