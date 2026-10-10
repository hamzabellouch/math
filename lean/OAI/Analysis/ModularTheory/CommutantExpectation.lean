import OAI.Analysis.ModularRecovery.ModularCovariance
import OAI.Analysis.ModularRecovery.CanonicalTomita
import OAI.Analysis.OperatorAlgebra.AntiunitaryCPConjugation
import OAI.Analysis.Nuclearity.NuclearQuotientExpectation
import OAI.Analysis.CharacterCriterion.FactorIndependence

namespace OAI

/-! Tomita conjugation transfers a cpc commutant projection to the von Neumann
algebra in a cyclic separating representation, including quotient
representations without assuming nuclearity or semidiscreteness of the quotient. -/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem modular_expectation_of_commutant_expectation
    (S : BoundedRecovery.StandardModularData H)
    (P : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (hP : CompletelyPositive P) (hPn : ‖P‖ ≤ 1)
    (hPr : ∀ T, P T ∈ S.M.commutant)
    (hPf : ∀ T, T ∈ S.M.commutant → P T = T) :
    ∃ E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H), CompletelyPositive E ∧ ‖E‖ ≤ 1 ∧
      (∀ T, E T ∈ S.M) ∧ (∀ T, T ∈ S.M → E T = T) := by
  refine ⟨antiunitaryCPConjugate S.J P,
    antiunitaryCPConjugate_cp S.J S.conjugation P hP,
    (antiunitaryCPConjugate_norm_le S.J P).trans hPn, ?_, ?_⟩
  · intro T
    change S.jConjugate (P (S.jConjugate T)) ∈ S.M
    exact S.jConjugate_mem _ (hPr _)
  · intro T hT
    change S.jConjugate (P (S.jConjugate T)) = T
    rw [hPf _ (S.jConjugate_mem_commutant T hT), S.jConjugate_involutive]

variable {A Q : Type*} [CStarAlgebra A] [CStarAlgebra Q]
  [PartialOrder A] [StarOrderedRing A]

open KirchbergRordam.GenericRW.GroupedFactors

omit [PartialOrder A] [StarOrderedRing A] in
lemma representation_bicommutant_commutant (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) :
    T ∈ (bicommutant π.range).commutant ↔ T ∈ representationCommutant π := by
  rw [bicommutant, VonNeumannAlgebra.commutant_commutant, mem_commutantOf_iff]
  constructor
  · intro h
    apply mem_representationCommutant π T
    intro a
    exact (h (π a) ⟨a, rfl⟩).symm
  · intro h a ha
    obtain ⟨x, rfl⟩ := ha
    exact representationCommutant_commute π x ⟨T, h⟩

/-- The cyclic separating representation of a quotient of a nuclear algebra
has a cpc projection onto its represented von Neumann algebra. -/
theorem nuclear_quotient_standard_expectation [Nontrivial H] (hA : Nuclear A)
    (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q) (π : Q →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : BoundedRecovery.CyclicSeparatingData H) (hS : S.M = bicommutant π.range) :
    ∃ E : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H), CompletelyPositive E ∧ ‖E‖ ≤ 1 ∧
      (∀ T, E T ∈ S.M) ∧ (∀ T, T ∈ S.M → E T = T) := by
  obtain ⟨P, hP, hPn, hPr, hPf⟩ := nuclear_quotient_commutant_expectation hA q hq π
  apply modular_expectation_of_commutant_expectation S.toStandardModularData P hP hPn
  · intro T
    change P T ∈ S.M.commutant
    rw [hS, representation_bicommutant_commutant]
    exact hPr T
  · intro T hT
    apply hPf T
    change T ∈ S.M.commutant at hT
    rwa [hS, representation_bicommutant_commutant] at hT

end WeakPureInfiniteness

end

end OAI
