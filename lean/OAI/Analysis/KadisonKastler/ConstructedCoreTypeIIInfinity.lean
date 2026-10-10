import OAI.Analysis.KadisonKastler.CoreWindowDualComparison
import OAI.Analysis.KadisonKastler.FiniteFactorAutomorphismProjection
import OAI.Analysis.KadisonKastler.MinimalProjectionEquivalence
import OAI.Analysis.KadisonKastler.TypeIFactorStability
import OAI.Analysis.KadisonKastler.InfiniteFactorProperInfiniteness
import Mathlib.MeasureTheory.Measure.SeparableMeasure

namespace OAI

/-! # A factorial constructed modular core is type II infinity

The dual action rescales the faithful trace on a bounded-frequency corner.
Minimal projections and finite diffuse factors would instead preserve
projection equivalence. Both alternatives are excluded by the local scaling.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

local instance coreTypeNontrivial : Nontrivial (RegularCoreHilbert H) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  apply nontrivial_of_ne (unitFrequencyVector x) 0
  intro he
  have hn := norm_unitFrequencyVector x
  rw [he, norm_zero] at hn
  exact hx (norm_eq_zero.mp hn.symm)

local instance coreTypeTwoFinite : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

theorem constructedCore_not_typeI
    (hf : ScalarCenter (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M)) :
    ¬ IsTypeIFactor (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M) := by
  intro htype
  let U := modularStrongGroup J Ω hsep hcyc
  let hU := modularStrongGroup_continuous J Ω hsep hcyc
  let h := coreFrequencyProjection U hU M 0 (1 / 2)
  have hh0 : h.val ≠ 0 := by
    intro hz
    exact regularFrequencyWindow_half_ne_zero (H := H) (congrArg Subtype.val hz)
  obtain ⟨p, hp⟩ := htype.minimal
  obtain ⟨q, hqh, hq⟩ := factor_exists_minimal_below hf p hp h hh0
  let e := constructedCoreDualEquiv J Ω hsep hcyc (2 * Real.pi * (1 / 2))
  exact constructedCore_subhalf_not_equivalent_dual J Ω hsep hcyc q hq.1 hqh
    (factor_minimal_projections_equivalent hf q (mapAlgebraProjection e q) hq
      (minimalProjection_map e q hq))

theorem constructedCore_not_II1 :
    ¬ Generator.IsII1Factor
      (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
        (modularStrongGroup_continuous J Ω hsep hcyc) M).toStarSubalgebra := by
  intro hfinite
  let q := coreFrequencyProjection (modularStrongGroup J Ω hsep hcyc)
    (modularStrongGroup_continuous J Ω hsep hcyc) M 0 (1 / 2)
  have hq0 : q.val ≠ 0 := by
    intro hz
    exact regularFrequencyWindow_half_ne_zero (H := H) (congrArg Subtype.val hz)
  exact constructedCore_subhalf_not_equivalent_dual J Ω hsep hcyc q hq0 le_rfl
    (equivalent_automorphism_projection hfinite
      (constructedCoreDualEquiv J Ω hsep hcyc (2 * Real.pi * (1 / 2))) q)

theorem constructedCore_not_finite
    (hf : ScalarCenter (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M)) :
    ¬ FiniteProjectionIn (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M) 1 := by
  intro hfinite
  exact constructedCore_not_II1 J Ω hsep hcyc
    (isII1Factor_of_finite_of_not_typeI hf zero_ne_one hfinite
      (constructedCore_not_typeI J Ω hsep hcyc hf))

theorem constructedFactorialCore_typeIIInfinity
    (hf : ScalarCenter (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M)) :
    TypeIIInfinityFactor (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M) where
  factor := hf
  properlyInfinite := publishedInfiniteFactorProperlyInfinite _ _ hf
    (constructedCore_not_finite J Ω hsep hcyc hf)
  semifinite := constructedFactorialCore_projectionSemifinite J Ω hsep hcyc hf
  diffuse := (isTypeIFactor_or_projectionDiffuse hf).resolve_left
    (constructedCore_not_typeI J Ω hsep hcyc hf)

end

end KadisonKastler

end OAI
