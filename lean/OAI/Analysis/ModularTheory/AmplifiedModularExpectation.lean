import OAI.Analysis.OperatorAlgebra.ScalarOperatorSlices
import OAI.Analysis.OperatorAlgebra.PointwiseTomita

namespace OAI

/-! An actual expectation onto the infinite scalar amplification of the
standard von Neumann algebra of a nuclear quotient. It is obtained from the
proved commutant projection in the amplified representation and pointwise
Tomita conjugation, rather than from an unproved normal tensor extension. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexOrder CStarAlgebra

namespace WeakPureInfiniteness
open KirchbergRordam.GenericRW.GroupedFactors

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure ℝ)

def amplifiedModularAlgebra (S : BoundedRecovery.StandardModularData H) :
    VonNeumannAlgebra (Lp H 2 μ) :=
  commutantOf (((pointwiseLpRepresentation μ).comp S.M.commutant.toStarSubalgebra.subtype).range)

lemma mem_amplifiedModularAlgebra (S : BoundedRecovery.StandardModularData H)
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) :
    T ∈ amplifiedModularAlgebra μ S ↔
      ∀ b, b ∈ S.M.commutant → Commute (pointwiseLpRepresentation μ b) T := by
  rw [amplifiedModularAlgebra, mem_commutantOf_iff]
  constructor
  · intro h b hb
    exact h _ ⟨⟨b, hb⟩, rfl⟩
  · intro h a ha
    obtain ⟨b, rfl⟩ := ha
    exact h b.val b.property

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A]

theorem nuclear_quotient_amplified_expectation [Nontrivial (Lp H 2 μ)]
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] B) (hq : Function.Surjective q)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : BoundedRecovery.StandardModularData H)
    (hS : S.M = bicommutant π.range) :
    ∃ E : (Lp H 2 μ →L[ℂ] Lp H 2 μ) →L[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ),
      CompletelyPositive E ∧ ‖E‖ ≤ 1 ∧
      (∀ T, E T ∈ amplifiedModularAlgebra μ S) ∧
      (∀ T, T ∈ amplifiedModularAlgebra μ S → E T = T) := by
  let ρ := (pointwiseLpRepresentation μ).comp π
  obtain ⟨P, hP, hPn, hPr, hPf⟩ := nuclear_quotient_commutant_expectation hA q hq ρ
  let J := pointwiseAntiunitary μ S.J
  have hJ : Function.Involutive J := pointwiseAntiunitary_involutive μ S.J S.conjugation
  refine ⟨antiunitaryCPConjugate J P, antiunitaryCPConjugate_cp J hJ P hP,
    (antiunitaryCPConjugate_norm_le J P).trans hPn, ?_, ?_⟩
  · intro T
    apply (mem_amplifiedModularAlgebra μ S _).mpr
    intro b hb
    apply (pointwiseTomita_commute_iff μ S b _).mpr
    apply pointwise_commutation_extends_bicommutant μ π
    · intro a
      exact representationCommutant_commute ρ a ⟨_, hPr _⟩
    · rw [← hS]
      exact S.jConjugate_mem b hb
  · intro T hT
    have ht : antiunitaryConjugate J T ∈ representationCommutant ρ := by
      apply mem_representationCommutant ρ
      intro a
      apply Commute.symm
      apply (pointwiseTomita_commute_iff μ S (π a) T).mpr
      apply (mem_amplifiedModularAlgebra μ S T).mp hT
      apply S.jConjugate_mem_commutant
      rw [hS]
      exact subset_bicommutant π.range (π a) ⟨a, rfl⟩
    change antiunitaryConjugate J (P (antiunitaryConjugate J T)) = T
    rw [hPf _ ht, antiunitaryConjugate_involutive J hJ]

end WeakPureInfiniteness

end

end OAI
