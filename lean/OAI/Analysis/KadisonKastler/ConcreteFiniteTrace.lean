import OAI.Analysis.KadisonKastler.ConcreteTraceTransfer
import OAI.Analysis.FactorGeneration.NormalTrace

namespace OAI

/-! # The faithful normal trace of a concrete finite diffuse factor

The projection-dimension trace gives a faithful normal tracial state
on a concrete finite diffuse factor.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

local instance finiteTraceOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance finiteTracePreorder : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
local instance finiteTraceLE : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance finiteTraceStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

private theorem factor_central (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (c : Algebra M) (hc : ∀ a : Algebra M, a * c = c * a) :
    ∃ z : ℂ, c = z • (1 : Algebra M) := by
  obtain ⟨z, hz⟩ := hM.factor c hc
  exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩

private theorem factor_one_ne_zero (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    (1 : Algebra M) ≠ 0 := by
  intro h
  exact hM.nonzero (congrArg Subtype.val h).symm

/-- The trace is a complex-valued faithful tracial state with the
continuity required by amplification. -/
def concreteFactorTrace (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    FaithfulTracialState (Algebra M) where
  toLinearMap := (Generator.Tracial.traceFreeTrace (factor_central hM) hM.diffuse hM.finite
    (factor_one_ne_zero hM)).toLinearMap
  map_one := (Generator.Tracial.traceFreeTrace_spec (factor_central hM) hM.diffuse hM.finite
    (factor_one_ne_zero hM)).2.1
  positive x := (Generator.Tracial.traceFreeTrace_spec (factor_central hM) hM.diffuse hM.finite
    (factor_one_ne_zero hM)).2.2.1 _ (star_mul_self_nonneg _)
  positive_im x := by
    have h := (Generator.Tracial.traceFreeTrace_spec (factor_central hM) hM.diffuse hM.finite
      (factor_one_ne_zero hM)).2.2.2.1 (star x * x)
    rw [star_mul, star_star] at h
    have hi := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at hi
    have hz : ((Generator.Tracial.traceFreeTrace (factor_central hM) hM.diffuse hM.finite
      (factor_one_ne_zero hM)) (star x * x)).im = 0 := by linarith
    exact hz
  faithful x hx := by
    have hs := (Generator.Tracial.traceFreeTrace_faithful (factor_central hM) hM.diffuse hM.finite
      (factor_one_ne_zero hM) (star x * x) (star_mul_self_nonneg _)).mp hx
    exact (CStarRing.star_mul_self_eq_zero_iff x).mp hs
  tracial := (Generator.Tracial.traceFreeTrace_spec (factor_central hM) hM.diffuse hM.finite
    (factor_one_ne_zero hM)).2.2.2.2

/-- Its finite vector-functional expression is also already proved in
the concrete representation in which the factor was supplied. -/
theorem concreteFactorTrace_finiteVector (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    FiniteVectorTrace (concreteFactorTrace hM) := by
  obtain ⟨n, ξ, η, h⟩ := Generator.Tracial.traceFreeTrace_finite_vector_representation
    (factor_central hM) hM.diffuse hM.finite (factor_one_ne_zero hM)
  exact ⟨n, ξ, η, h⟩

/-- The normal trace transfers two-small bounded elements to strongly
small operators in the original concrete representation. -/
theorem concreteFactorTrace_strongContinuous (hM : Generator.IsII1Factor M.toStarSubalgebra) :
    TraceStrongContinuous (concreteFactorTrace hM) M.toStarSubalgebra.subtype :=
  (concreteFactorTrace_finiteVector hM).strongContinuous

end

end KadisonKastler

end OAI
