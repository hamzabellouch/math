import Mathlib
import OAI.Analysis.Commutator.ChoiGNS
import OAI.Analysis.Commutator.ChoiRecovery
import OAI.Analysis.Commutator.CpCompression

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

namespace Kadison.OperatorSystem

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {ι : Type} [Fintype ι] [Nonempty ι]

local instance : DecidableEq ι := Classical.decEq ι

theorem exists_finite_extension (S : Submodule ℂ A) (h1 : (1 : A)∈S)
    (hs : ∀ a∈S,star a∈S)
    (f : S →ₗ[ℂ] (CoordinateSpace ι →L[ℂ] CoordinateSpace ι))
    (hf : IsCompletelyPositive S f) :
    ∃ Φ : A →CP (CoordinateSpace ι →L[ℂ] CoordinateSpace ι),∀ a : S,Φ a=f a := by
  obtain ⟨η,hη⟩ := exists_choi_extension S h1 hs f hf
  let i₀ : ι := Classical.choice inferInstance
  refine ⟨CpCompression.compression (choiRepresentation η) (choiEmbedding η i₀),?_⟩
  intro a
  apply basis_inner_ext
  intro i j
  change ⟪basisVector i,(choiEmbedding η i₀).adjoint
    (choiRepresentation η a (choiEmbedding η i₀ (basisVector j)))⟫_ℂ=_
  rw [choi_coefficient]
  calc
    η (ChoiGNS.entry i j (a : A)) = choi S f (systemEntry S a i j) := by simpa only [systemEntry] using hη (systemEntry S a i j)
    _ = _ := choi_systemEntry S f a i j

omit [Nonempty ι] in
theorem exists_finite_extension_all (S : Submodule ℂ A) (h1 : (1 : A)∈S)
    (hs : ∀ a∈S,star a∈S)
    (f : S →ₗ[ℂ] (CoordinateSpace ι →L[ℂ] CoordinateSpace ι))
    (hf : IsCompletelyPositive S f) :
    ∃ Φ : A →CP (CoordinateSpace ι →L[ℂ] CoordinateSpace ι),∀ a : S,Φ a=f a := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let Φ : A →CP (CoordinateSpace ι →L[ℂ] CoordinateSpace ι) :=
      { toLinearMap := 0
        map_cstarMatrix_nonneg' := by
          intro n X hX
          have he : X.map (0 : A →ₗ[ℂ] (CoordinateSpace ι →L[ℂ] CoordinateSpace ι))=0 := by
            ext i j
            rfl
          rw [he] }
    exact ⟨Φ,fun _ => Subsingleton.elim _ _⟩
  | inr h => exact exists_finite_extension S h1 hs f hf

end Kadison.OperatorSystem

end

end
end

end OAI
