import OAI.Analysis.KadisonKastler.FullCopyHilbertSum
import OAI.Analysis.KadisonKastler.TypeIIICyclicSeparating

namespace OAI

/-! # Countable amplification is spatially absorbed by a type III representation -/

namespace KadisonKastler

open Generator.Tracial
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem TypeIIIFactor.commutant_properlyInfinite (hM : TypeIIIFactor M) :
    ProperlyInfiniteIdentity M.commutant := by
  obtain ⟨ξ,_,hc,hs⟩ := hM.exists_cyclic_separating_unit_vector
  obtain ⟨J,_⟩ := exists_hilbert_conjugation (H := H)
  let d := constructedModularConjugationData J ξ hs hc
    (tomitaPolarConjugation_commutant_eq J ξ hs hc)
  obtain ⟨v,hv,hproper⟩ := hM.exists_proper_isometry
  let w : Algebra M.commutant := ⟨conjugationOperator d.conjugation v.val,d.right_mem le_rfl v⟩
  have hw : star w*w=1 := by
    apply Subtype.ext
    change star (conjugationOperator d.conjugation v.val)*conjugationOperator d.conjugation v.val=1
    rw [← conjugationOperator_star _ d.involutive,← conjugationOperator_mul _ d.involutive]
    rw [show star v.val*v.val=1 from congrArg Subtype.val hv,
      conjugationOperator_one _ d.involutive]
  have hp : w*star w≠1 := by
    intro he
    have he' := congrArg (fun a : Algebra M.commutant => conjugationOperator d.conjugation a.val) he
    change conjugationOperator d.conjugation
      (conjugationOperator d.conjugation v.val*star (conjugationOperator d.conjugation v.val))=
      conjugationOperator d.conjugation 1 at he'
    rw [← conjugationOperator_star _ d.involutive,← conjugationOperator_mul _ d.involutive,
      conjugationOperator_twice _ d.involutive,conjugationOperator_one _ d.involutive] at he'
    exact hproper (Subtype.ext he')
  exact properlyInfiniteIdentity_of_proper_isometry (scalarCenter_commutant M hM.factor) w hw hp

theorem TypeIIIFactor.exists_countable_amplification_unitary (hM : TypeIIIFactor M) :
    ∃ U : CountableHilbertSum H ≃ₗᵢ[ℂ] H,
      ∀ (a : Algebra M) (x : CountableHilbertSum H), U (l2Diagonal a.val x)=a.val (U x) := by
  let p : AlgebraProjection M.commutant := ⟨1,IsStarProjection.one _⟩
  have hp : (centralSupport p).val=1 := by
    have he := le_centralSupport p
    change (centralSupport p).val*1=1 at he
    simpa only [mul_one] using he
  obtain ⟨C⟩ := exists_countable_projection_copies hM.commutant_properlyInfinite p hp
  refine ⟨C.fullCopyUnitary,?_⟩
  intro a x
  exact C.fullCopyUnitary_intertwines a.val (fun i =>
    VonNeumannAlgebra.mem_commutant_iff.mp (C.witness i).property a.val a.property) x

end
end KadisonKastler

end OAI
