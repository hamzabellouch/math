import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SubgroupResolution
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

namespace OAI

/-! # Homology vanishing above the integral dimension bound -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G]

theorem groupHomology_isZero_above_dimension (d : ℕ)
    [HasProjectiveDimensionLE (trivialIntegral G) d]
    (A : Rep ℤ G) (i : ℕ) (hi : d < i) : IsZero (groupHomology A i) := by
  classical
  let P := finiteProjectiveResolution (Rep.standardResolution ℤ G) d
  have hP : IsZero (P.complex.X i) :=
    finiteTruncation_isZero (Rep.standardResolution ℤ G) d i hi
  have hX : IsZero ((P.complex.coinvariantsTensorObj A).X i) :=
    ((Rep.coinvariantsTensor ℤ G).obj A).map_isZero hP
  refine IsZero.of_iso ?_ (groupHomologyIso A i P)
  apply HomologicalComplex.ExactAt.isZero_homology
  apply ShortComplex.exact_of_isZero_X₂
  simpa only [HomologicalComplex.shortComplexFunctor_obj_X₂] using hX

end PolycyclicRecognition

end

end OAI
