import OAI.CategoryTheory.Thomason.Simplicial.FinitePosetUnitReduction
import OAI.CategoryTheory.Thomason.Simplicial.TruncatedLocalPresentability
import OAI.CategoryTheory.Thomason.Strict.OrientalFiniteCells
import OAI.CategoryTheory.Thomason.Transfer.ThomasonQuillenBridge

namespace OAI

section

/-! # Filtered colimits for the actual Street nerve and Thomason weak class

Every degree of the Street nerve is represented by the corresponding finite
oriental. Thus the actual nerve and twice-extension nerve preserve filtered
colimits, in omega dimension and all finite dimensions. The realization
weak-equivalence class is consequently closed under these colimits.
-/

namespace Thomason.Construction

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

instance realization_inverseImage_stableUnderFilteredColimits
    {C : Type u} [Category.{v} C] (R : C ⥤ SSet.{0})
    [PreservesFilteredColimitsOfSize.{0,0} R] :
    (realizationWeakEquivalences.inverseImage R).IsStableUnderFilteredColimits.{0,0} where
  isStableUnderColimitsOfShape _ := ⟨by
    intro D E c d hc hd η hη p hp
    change realizationWeakEquivalences (R.map p)
    apply realization_filtered_colimit_weak (isColimitOfPreserves R hc)
      (isColimitOfPreserves R hd) (Functor.whiskerRight η R) (R.map p)
    · intro j
      change R.map (c.ι.app j) ≫ R.map p = R.map (η.app j) ≫ R.map (d.ι.app j)
      simpa only [← R.map_comp] using congrArg R.map (hp j)
    · exact hη⟩

namespace NormalizedSimplexIdentities

variable (h : NormalizedSimplexIdentities)

instance object_finite (n : ℕ) : Finite (h.object n) :=
  inferInstanceAs (Finite (SimplexComplex.oriental n (h.squared n)))

def streetNerveEvaluationIso (d : SimplexCategoryᵒᵖ) :
    h.streetNerve ⋙ SSet.evaluation.obj d ≅
      coyoneda.obj (Opposite.op (h.object d.unop.len)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro X Y f; rfl)

instance streetNerve_preservesFilteredColimitsOfShape
    {K : Type} [Category.{0} K] [IsFiltered K] :
    PreservesColimitsOfShape K h.streetNerve := by
  apply preservesColimitsOfShape_of_evaluation
  intro d
  exact preservesColimitsOfShape_of_natIso (h.streetNerveEvaluationIso d).symm

instance streetNerve_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{0,0} h.streetNerve where
  preserves_filtered_colimits _K := inferInstance

instance finiteStreetNerve_preservesFilteredColimitsOfShape (n : ℕ)
    {K : Type} [Category.{0} K] [IsFiltered K] :
    PreservesColimitsOfShape K (h.finiteStreetNerve n) :=
  inferInstanceAs (PreservesColimitsOfShape K
    (StrictOmegaCategory.inclusion n ⋙ h.streetNerve))

instance finiteStreetNerve_preservesFilteredColimits (n : ℕ) :
    PreservesFilteredColimitsOfSize.{0,0} (h.finiteStreetNerve n) where
  preserves_filtered_colimits _K := inferInstance

instance thomasonRight_preservesFilteredColimitsOfShape [StrictColimitsInput]
    {K : Type} [Category.{0} K] [IsFiltered K] :
    PreservesColimitsOfShape K h.thomasonRight :=
  inferInstanceAs (PreservesColimitsOfShape K (h.streetNerve ⋙ SSet.ex ⋙ SSet.ex))

instance thomasonRight_preservesFilteredColimits [StrictColimitsInput] :
    PreservesFilteredColimitsOfSize.{0,0} h.thomasonRight where
  preserves_filtered_colimits _K := inferInstance

instance streetWeakEquivalences_stableUnderFilteredColimits :
    h.streetWeakEquivalences.IsStableUnderFilteredColimits.{0,0} :=
  inferInstanceAs (MorphismProperty.IsStableUnderFilteredColimits.{0,0}
    (realizationWeakEquivalences.inverseImage h.streetNerve))

instance finiteStreetWeakEquivalences_stableUnderFilteredColimits (n : ℕ) :
    MorphismProperty.IsStableUnderFilteredColimits.{0,0}
      (realizationWeakEquivalences.inverseImage (h.finiteStreetNerve n)) := inferInstance

end NormalizedSimplexIdentities

namespace FiniteReflectionInput

variable (h : NormalizedSimplexIdentities) (n : ℕ) [StrictColimitsInput]

instance thomasonRight_preservesFilteredColimitsOfShape
    {K : Type} [Category.{0} K] [IsFiltered K] :
    PreservesColimitsOfShape K (thomasonRight (n := n) h) :=
  inferInstanceAs (PreservesColimitsOfShape K
    (h.finiteStreetNerve (n+1) ⋙ SSet.ex ⋙ SSet.ex))

instance thomasonRight_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{0,0} (thomasonRight (n := n) h) where
  preserves_filtered_colimits _K := inferInstance

instance thomasonWeakEquivalences_stableUnderFilteredColimits :
    (thomasonWeakEquivalences (n := n) h).IsStableUnderFilteredColimits.{0,0} :=
  inferInstanceAs (MorphismProperty.IsStableUnderFilteredColimits.{0,0}
    (realizationWeakEquivalences.inverseImage (h.finiteStreetNerve (n+1))))

end FiniteReflectionInput

end

end Thomason.Construction

end

end OAI
