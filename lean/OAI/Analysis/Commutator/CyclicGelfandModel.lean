import Mathlib
import OAI.Analysis.Commutator.CyclicSpectralUnitary

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory

open scoped Topology

namespace Kadison.CyclicSpectral

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev spectrumSpace := WeakDual.characterSpace ℂ A

variable [MeasurableSpace (spectrumSpace (A:=A))] [BorelSpace (spectrumSpace (A:=A))]

def gelfandRepresentation (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    C(spectrumSpace (A:=A),ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  ρ.comp (gelfandStarTransform A).symm.toStarAlgHom

omit [MeasurableSpace (spectrumSpace (A:=A))] [BorelSpace (spectrumSpace (A:=A))] in
lemma gelfandRepresentation_dense (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hd : DenseRange (fun a : A => ρ a ξ)) :
    DenseRange (orbitMap (gelfandRepresentation ρ) ξ) := by
  apply hd.mono
  rintro y ⟨a,rfl⟩
  refine ⟨gelfandStarTransform A a,?_⟩
  change ρ ((gelfandStarTransform A).symm (gelfandStarTransform A a)) ξ=ρ a ξ
  rw [(gelfandStarTransform A).symm_apply_apply]

theorem exists_gelfand_model (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hd : DenseRange (fun a : A => ρ a ξ)) :
    ∃ μ : Measure (spectrumSpace (A:=A)), IsFiniteMeasure μ ∧
      ∃ U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] H,
        ∀ (a : A) (v : Lp ℂ 2 μ), U (scalarMultiplier μ (gelfandStarTransform A a) v)=ρ a (U v) := by
  let σ := gelfandRepresentation ρ
  let μ := measure σ ξ
  let U := unitary σ ξ (gelfandRepresentation_dense ρ ξ hd)
  refine ⟨μ,inferInstance,U,?_⟩
  intro a v
  have h := unitary_intertwines σ ξ (gelfandRepresentation_dense ρ ξ hd)
    (gelfandStarTransform A a) v
  have he : σ (gelfandStarTransform A a)=ρ a := by
    change ρ ((gelfandStarTransform A).symm (gelfandStarTransform A a))=ρ a
    rw [(gelfandStarTransform A).symm_apply_apply]
  rw [he] at h
  exact h

end Kadison.CyclicSpectral

end

end
end

end OAI
