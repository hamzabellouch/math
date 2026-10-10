import OAI.Analysis.KadisonKastler.CenterAlgebra
import OAI.Analysis.FactorGeneration.MatrixSequence

namespace OAI

/-! # The type-II part of the published type stability lemma

Christensen--Sinclair--Smith--White, *Perturbations of C*-algebraic invariants*,
GAFA 20 (2010), 368--397, Lemma 3.5 (author manuscript pp. 9--10), proves
that two von Neumann algebras with the same centre and distance less than
`1/10` have the same finite type I, type II₁ and infinite central parts.
Here only diffuseness of the neighbour of a II₁ factor is retained.
The centre and finiteness conclusions are already proved locally.

Primary author manuscript: https://eprints.gla.ac.uk/25426/1/25426.pdf
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Two concrete scalar centres are literally the same algebra. -/
theorem concreteCenter_eq_of_scalar {M N : VonNeumannAlgebra H}
    (hM : ∀ c : Algebra M, (∀ a : Algebra M, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra M))
    (hN : ∀ c : Algebra N, (∀ a : Algebra N, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra N)) :
    concreteCenter M = concreteCenter N := by
  have hmem (P Q : VonNeumannAlgebra H)
      (hP : ∀ c : Algebra P, (∀ a : Algebra P, a * c = c * a) →
        ∃ z : ℂ, c = z • (1 : Algebra P))
      {x : H →L[ℂ] H} (hx : x ∈ concreteCenter P) : x ∈ concreteCenter Q := by
    change x ∈ P ∧ x ∈ P.commutant at hx
    obtain ⟨z, hz⟩ := hP ⟨x, hx.1⟩ (fun a => Subtype.ext
      (VonNeumannAlgebra.mem_commutant_iff.mp hx.2 a.val a.property))
    have he : x = z • (1 : H →L[ℂ] H) := congrArg Subtype.val hz
    rw [he]
    change z • (1 : H →L[ℂ] H) ∈ Q ∧ z • (1 : H →L[ℂ] H) ∈ Q.commutant
    exact ⟨Q.smul_mem Q.one_mem z, Q.commutant.smul_mem Q.commutant.one_mem z⟩
  apply VonNeumannAlgebra.ext
  intro x
  exact ⟨hmem M N hM, hmem N M hN⟩

/-- The application-specific part of CSSW (2010), Lemma 3.5. No spatial
equivalence or perturbation estimate is included in this published input. -/
def PublishedFiniteType : Prop :=
  ∀ (M N : VonNeumannAlgebra H), concreteCenter M = concreteCenter N →
    Generator.IsII1Factor M.toStarSubalgebra → kkDistance M N < 1 / 10 →
    ∀ p : Algebra N, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra N, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q

/-- Combining the published type conclusion with the proved finite-neighbour
and scalar-centre lemmas gives the II₁ predicate. -/
theorem isII1Factor_of_near_of_published
    (hpub : PublishedFiniteType (H := H)) {M N : VonNeumannAlgebra H}
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hgap : kkDistance M N < 1 / 10) :
    Generator.IsII1Factor N.toStarSubalgebra := by
  obtain ⟨hc, hf⟩ := finite_factor_of_near_II1 hM hgap
  have he : concreteCenter M = concreteCenter N := concreteCenter_eq_of_scalar
    (fun c hc => by
      obtain ⟨z, hz⟩ := hM.factor c hc
      exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩) hc
  exact {
    nonzero := hM.nonzero
    weaklyClosed := Generator.Tracial.vonNeumann_wotClosed N
    factor := fun c hcomm => by
      obtain ⟨z, hz⟩ := hc c hcomm
      exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
    finite := hf
    diffuse := hpub M N he hM hgap }

end

end KadisonKastler

end OAI
