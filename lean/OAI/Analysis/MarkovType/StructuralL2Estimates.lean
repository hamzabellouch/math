import OAI.Analysis.MarkovType.FailureJTriangular
import OAI.Analysis.MarkovType.JConvexityReflexivity
import OAI.Analysis.MarkovType.SequenceL2JConvex
import OAI.Analysis.MarkovType.FiniteL2CoefficientAdapter
import OAI.Analysis.MarkovType.FiniteMartingaleDuality
import OAI.Analysis.MarkovType.FiniteL2IsometryTransport
import OAI.Analysis.MarkovType.TriangularTransport
import OAI.Analysis.MarkovType.RenormedGeometry

namespace OAI

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem FiniteTriangularObstruction.sequenceL2
    (h : FiniteTriangularObstruction X) :
    FiniteTriangularObstruction (SequenceL2 X) :=
  h.ambientJConvex.sequenceL2.finiteTriangularObstruction

theorem finiteLowerL2_of_obstruction (h : FiniteTriangularObstruction X) :
    ∃ s : ℝ, 2 ≤ s ∧ ∃ χ : ℝ, 1 ≤ χ ∧ FiniteLowerL2 X s χ :=
  finiteLowerL2_of_sequence_obstruction h.sequenceL2

theorem finiteUpperL2_of_obstruction (h : FiniteTriangularObstruction X) :
    ∃ r : ℝ, 1 < r ∧ r ≤ 2 ∧ ∃ χ : ℝ, 1 ≤ χ ∧ FiniteUpperL2 X r χ := by
  have hDual : FiniteTriangularObstruction (StrongDual ℝ X) :=
    finiteTriangularObstruction_dual_iff.mp h
  obtain ⟨s, hs, χ, hχ, hLower⟩ := finiteLowerL2_of_obstruction hDual
  have hr := lowerL2_dual_exponent_range hs
  have hUpper := finiteLowerL2_dual_upper hs hχ hLower
  exact ⟨s / (s - 1), hr.1, hr.2, χ, hχ,
    hUpper.pullback_isometry (NormedSpace.inclusionInDoubleDualLi ℝ)⟩

theorem finiteTriangularObstruction_of_hasEquivalentUCNorm
    (h : HasEquivalentUCNorm X) : FiniteTriangularObstruction X := by
  obtain ⟨N, hN⟩ := h
  have hJ : AmbientJConvex (Renormed N) :=
    Renormed.ambientJConvex_of_uniformConvex N hN
  exact (finiteTriangularObstruction_equiv_iff
    (Renormed.continuousLinearEquiv N)).mpr hJ.finiteTriangularObstruction

theorem finiteTriangularObstruction_of_hasEquivalentUSNorm
    (h : HasEquivalentUSNorm X) : FiniteTriangularObstruction X := by
  obtain ⟨N, hN⟩ := h
  have hJ : AmbientJConvex (Renormed N) :=
    Renormed.ambientJConvex_of_uniformSmooth N hN
  exact (finiteTriangularObstruction_equiv_iff
    (Renormed.continuousLinearEquiv N)).mpr hJ.finiteTriangularObstruction

theorem finiteUpperL2_of_hasEquivalentUCNorm (h : HasEquivalentUCNorm X) :
    ∃ r : ℝ, 1 < r ∧ r ≤ 2 ∧ ∃ χ : ℝ, 0 < χ ∧ FiniteUpperL2 X r χ := by
  obtain ⟨r, hr, hr₂, χ, hχ, hUpper⟩ :=
    finiteUpperL2_of_obstruction (finiteTriangularObstruction_of_hasEquivalentUCNorm h)
  exact ⟨r, hr, hr₂, χ, lt_of_lt_of_le zero_lt_one hχ, hUpper⟩

end MarkovSuperreflexivity

end OAI
