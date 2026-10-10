import OAI.Analysis.KadisonKastler.MultiplicationCorrectionTransport
import OAI.Analysis.KadisonKastler.TypeIInjectivity
import OAI.Analysis.KadisonKastler.PublishedCorrection

namespace OAI

/-! # Multiplication correction for type I factors

The minimal cyclic model identifies the factor with all bounded operators.
The constructed correction is transported back without changing its complete
norm, in every represented multiplicity.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance typeICorrectionOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance typeICorrectionStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem IsTypeIFactor.publishedMultiplicationCorrection (hM : IsTypeIFactor M) :
    PublishedMultiplicationCorrection M := by
  obtain ⟨p, hp⟩ := hM.minimal
  obtain ⟨ξ, hξ, hpξ⟩ := exists_nonzero_fixed_vector p hp.1
  let K := typeICyclicSpace M ξ
  have hK : Nontrivial K := by
    apply nontrivial_of_ne (typeICyclicVector M ξ) 0
    intro h
    exact hξ (congrArg Subtype.val h)
  let : Nontrivial K := hK
  let e : Algebra M ≃⋆ₐ[ℂ] (K →L[ℂ] K) :=
    typeICyclicEquiv hM.factor p hp ξ hξ hpξ
  intro m hm hms q hq hq1 hb
  obtain ⟨L, hLm, hLs, hLb⟩ :=
    multiplication_correction_of_operator_model e m hm hms hq hq1 hb
  exact ⟨L, hLm, hLs, hLb.mono (by linarith)⟩

end

end KadisonKastler

end OAI
