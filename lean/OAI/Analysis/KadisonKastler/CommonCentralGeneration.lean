import OAI.Analysis.KadisonKastler.RepresentationCommutantInclusion
import OAI.Analysis.KadisonSimilarity.Tracial.JointCStarSource
import OAI.Analysis.KadisonSimilarity.Tracial.CentralCStarSource

namespace OAI

/-! # The joint source generates the central commutant -/

namespace KadisonKastler

open KadisonSimilarity

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem representation_joint_eq_center_commutant (M : VonNeumannAlgebra H)
    (A C : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (A : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
    (hA : generatedVonNeumannAlgebra A = M)
    (hC : (starSubalgebraCommutant C).commutant = M.commutant)
    (hAM : A ≤ M.toStarSubalgebra) (hCM : C ≤ M.commutant.toStarSubalgebra) :
    representationVonNeumannAlgebra (jointCStarSource A C).subtype =
      (vonNeumannCenter M).commutant := by
  have hAg : (starSubalgebraCommutant A).commutant = M := by
    simpa only [representationVonNeumannAlgebra, subtype_star_range, hA] using
      (representationVonNeumannAlgebra_eq_generated A.subtype)
  change (starSubalgebraCommutant (jointCStarSource A C).subtype.range).commutant = _
  rw [subtype_star_range]
  exact jointCStarSource_bicommutant M A C hAM hCM hAg hC

end

end KadisonKastler

end OAI
