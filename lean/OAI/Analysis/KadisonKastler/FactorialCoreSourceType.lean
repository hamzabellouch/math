import OAI.Analysis.KadisonKastler.SemifiniteCoreCenter
import OAI.Analysis.KadisonKastler.TypeICoreCenter
import OAI.Analysis.KadisonKastler.II1CoreCenter
import OAI.Analysis.KadisonKastler.InfiniteFactorProperInfiniteness
import OAI.Analysis.KadisonKastler.ProjectionSemifiniteness
import OAI.Analysis.KadisonKastler.ModularCoreTypeIIInfinity

namespace OAI

/-! # A factorial modular core forces the source factor to be type III -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem typeIII_of_factorialCore (hM : ScalarCenter M) (Ω : H)
    (hs : Function.Injective (algebraVectorMap M Ω))
    (hc : DenseRange (algebraVectorMap M Ω))
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hn : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hm : IsModularStateGroup M Ω U)
    (hf : ScalarCenter (regularCoreAlgebra U hU M)) : TypeIIIFactor M := by
  have ht : ¬ IsTypeIFactor M := fun h => regularCore_not_factor_of_typeI h Ω hs hc U hU hn hm hf
  have hfinite : ¬ FiniteProjectionIn M 1 := by
    intro h
    exact regularCore_not_factor_of_II1
      (isII1Factor_of_finite_of_not_typeI hM zero_ne_one h ht) Ω hs hc U hU hn hm hf
  have hproper := publishedInfiniteFactorProperlyInfinite H M hM hfinite
  refine ⟨one_ne_zero, hM, ?_⟩
  intro p hp hpfinite
  by_contra hp0
  have hII : TypeIIInfinityFactor M := {
    factor := hM
    properlyInfinite := hproper
    semifinite := projectionSemifinite_of_finite_projection hM ⟨p, hp⟩ hp0 hpfinite
    diffuse := (isTypeIFactor_or_projectionDiffuse hM).resolve_left ht }
  exact regularCore_not_factor_of_typeIIInfinity hII Ω hs hc U hU hn hm hf

theorem publishedFactorialModularCore : PublishedFactorialModularCore.{u} := by
  intro H _ _ _ _ _ M hM Ω _ hc hs U hU hn hm hf
  exact typeIII1_of_typeIII_of_factorialCore
    (typeIII_of_factorialCore hM Ω hs hc U hU hn hm hf) Ω hs hc U hU hn hm hf

end

end KadisonKastler

end OAI
