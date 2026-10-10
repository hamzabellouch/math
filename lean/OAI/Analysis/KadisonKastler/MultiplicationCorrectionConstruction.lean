import OAI.Analysis.KadisonKastler.SimultaneousRowUltralimit
import OAI.Analysis.KadisonKastler.MultiplicationCorrectionFromRows

namespace OAI

/-! # Ricard--Roydor multiplication correction

The common modular row limit and complete-norm Newton iteration give
the correction and its quantitative bound.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance correctionConstructionOrder (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance correctionConstructionStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem publishedMultiplicationCorrection (M : VonNeumannAlgebra H) :
    PublishedMultiplicationCorrection M := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    intro m _ _ q hq _ _
    refine ⟨LinearEquiv.refl ℂ (Algebra M), fun _ _ => Subsingleton.elim _ _,
      fun _ => Subsingleton.elim _ _, ?_⟩
    have he : (LinearEquiv.refl ℂ (Algebra M)).toLinearMap - LinearMap.id = 0 := by
      ext a
      simp
    rw [he]
    intro p r X
    rw [matrix_map_zero, norm_zero]
    positivity
  · let := hH
    obtain ⟨ω, n, r, hr, hm⟩ := exists_universal_modular_rows M
    exact publishedMultiplicationCorrection_of_modular_rows M ω n r hr hm

end

end KadisonKastler

end OAI
