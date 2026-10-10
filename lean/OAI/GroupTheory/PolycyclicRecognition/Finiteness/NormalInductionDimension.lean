import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalInductionExact
import OAI.GroupTheory.PolycyclicRecognition.Algebra.InductionTrivial
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicQuotientSequence

namespace OAI

/-! # The cohomological dimension bound in an infinite cyclic extension -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G]

theorem projectiveDimension_of_boundedResolution {A : Rep ℤ G}
    (P : ProjectiveResolution A) (d : ℕ)
    (hz : ∀ i, d < i → IsZero (P.complex.X i)) :
    HasProjectiveDimensionLE A d := by
  let := HasExt.standard (Rep ℤ G)
  refine HasProjectiveDimensionLT.mk ?_
  intro i hi Y e
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (i + 1) rfl
  have hzero : f = 0 := (hz i (Nat.lt_of_succ_le hi)).eq_of_src f 0
  subst f
  exact P.extMk_zero (i + 1) rfl

theorem normalInducedResolution_bounded (N : Subgroup G) [N.Normal]
    {A : Rep ℤ N} (P : ProjectiveResolution A) (d : ℕ)
    (hz : ∀ i, d < i → IsZero (P.complex.X i)) :
    ∀ i, d < i → IsZero ((normalInducedResolution ℤ N P).complex.X i) := by
  intro i hi
  exact (Rep.indFunctor ℤ N.subtype).map_isZero (hz i hi)

theorem quotientRegular_projectiveDimension (N : Subgroup G) [N.Normal]
    (P : ProjectiveResolution (trivialIntegral N)) (d : ℕ)
    (hz : ∀ i, d < i → IsZero (P.complex.X i)) :
    HasProjectiveDimensionLE (Rep.res (QuotientGroup.mk' N)
      (Rep.leftRegular ℤ (G ⧸ N))) d := by
  let := projectiveDimension_of_boundedResolution (normalInducedResolution ℤ N P) d
    (normalInducedResolution_bounded N P d hz)
  exact hasProjectiveDimensionLT_of_iso (inductionTrivialIso ℤ N) (d + 1)

theorem cohomologicalDimension_of_infiniteCyclicQuotient
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] [Infinite (G ⧸ N)]
    (hN : HasFiniteProjectiveResolution N) : HasFiniteIntegralCohomologicalDimension G := by
  let : CommGroup (G ⧸ N) := IsCyclic.commGroup
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  obtain ⟨P, d, _, hd⟩ := hN
  let := quotientRegular_projectiveDimension N P d hd
  exact ⟨d + 1, cohomologicalDimension_bound_of_cyclicQuotientModule
    (G ⧸ N) (QuotientGroup.mk' N) z hz d⟩

end PolycyclicRecognition

end

end OAI
