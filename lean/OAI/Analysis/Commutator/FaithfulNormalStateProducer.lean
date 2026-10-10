import Mathlib
import OAI.Analysis.Commutator.FaithfulNormalFunctional
import OAI.Analysis.Commutator.NormalGNS

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology ComplexOrder

namespace Kadison

namespace FaithfulNormalFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (x : ℕ → H) (M : VonNeumannAlgebra H)

def restricted : M →ₚ[ℂ] ℂ where
  toFun a := functional x (a : H →L[ℂ] H)
  map_add' _ _ := (functional x).map_add _ _
  map_smul' _ _ := (functional x).map_smul _ _
  monotone' := fun _ _ h => (functional x).monotone h

lemma restricted_faithful (hd : DenseRange x) (a : M)
    (hz : restricted x M (star a*a)=0) : a=0 :=
  Subtype.ext (functional_faithful x hd (a : H →L[ℂ] H) hz)

lemma restricted_normal : NormalGNS.BoundedWOTContinuous M (restricted x M) := by
  intro C
  let f : {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} →
      {T : H →WOT[ℂ] H // ‖T.toCLM‖≤C} := fun a => ⟨a.val,a.property.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk (fun a => a.property.2)
  exact (functional_boundedWOT x C).comp hf

end FaithfulNormalFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_faithful_normal_positive [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) :
    ∃ τ : M →ₚ[ℂ] ℂ, NormalGNS.BoundedWOTContinuous M τ ∧
      ∀ a : M,τ (star a*a)=0 → a=0 := by
  obtain ⟨x,hx⟩ := TopologicalSpace.exists_dense_seq H
  exact ⟨FaithfulNormalFunctional.restricted x M,
    FaithfulNormalFunctional.restricted_normal x M,
    FaithfulNormalFunctional.restricted_faithful x M hx⟩

end Kadison

end

end
end

end OAI
