import OAI.Analysis.KadisonKastler.TypeIIICyclicSeparating

namespace OAI

/-! # Modular conjugation on the original type III representation -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem ModularConjugationData.left_mem {M : VonNeumannAlgebra H} {ξ : H}
    (d : ModularConjugationData M ξ) (a : Algebra M.commutant) :
    conjugationOperator d.conjugation a.val ∈ M := by
  have ha : a.val ∈ (conjugateRightAlgebra d.conjugation d.involutive M :
      Set (H →L[ℂ] H)) := by
    rw [d.commutant]
    exact a.property
  obtain ⟨b,hb,hba⟩ := ha
  rw [← hba,conjugationOperator_twice _ d.involutive]
  exact hb

theorem TypeIIIFactor.exists_standard_unit_vector
    [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    {M : VonNeumannAlgebra H} (hM : TypeIIIFactor M) :
    ∃ ξ : H, ‖ξ‖ = 1 ∧ DenseRange (algebraVectorMap M ξ) ∧
      Function.Injective (algebraVectorMap M ξ) ∧ Nonempty (ModularConjugationData M ξ) := by
  obtain ⟨ξ,hξ,hcyc,hsep⟩ := hM.exists_cyclic_separating_unit_vector
  obtain ⟨d,_⟩ := (publishedModularSpectralResolution H M ξ hcyc hsep).some
  exact ⟨ξ,hξ,hcyc,hsep,⟨d⟩⟩

end

end KadisonKastler

end OAI
