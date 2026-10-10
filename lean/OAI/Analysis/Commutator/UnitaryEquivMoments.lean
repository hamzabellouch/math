import Mathlib
import OAI.Analysis.Commutator.FreeSequenceUnitary

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open FinitePatching FinitePatching.Words FinitePatching.ConjugatedWords

variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

def pullUnitary (e : A ≃⋆ₐ[ℂ] B) (u : unitary B) : unitary A :=
  ⟨e.symm u,Unitary.map_mem e.symm.toStarAlgHom u.property⟩

lemma map_pullUnitary (e : A ≃⋆ₐ[ℂ] B) (u : unitary B) :
    (PartialUnitary.ofUnitary (pullUnitary e u)).map e.toStarAlgHom=PartialUnitary.ofUnitary u := by
  rw [PartialUnitary.map_ofUnitary]
  congr 1
  apply Subtype.ext
  exact e.apply_symm_apply u

lemma word_pullUnitary {J K : Type} (e : A ≃⋆ₐ[ℂ] B) (u : unitary B)
    (x : J → A) (k : K → ℤ) (l : List (Letter J K)) :
    e (word x k (PartialUnitary.ofUnitary (pullUnitary e u)) l)=
      word (e ∘ x) k (PartialUnitary.ofUnitary u) l := by
  rw [show e (word x k (PartialUnitary.ofUnitary (pullUnitary e u)) l)=
    word (e ∘ x) k ((PartialUnitary.ofUnitary (pullUnitary e u)).map e.toStarAlgHom) l from
    map_word e.toStarAlgHom x k _ l,map_pullUnitary]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

lemma pullUnitary_moment_limits (e : A ≃⋆ₐ[ℂ] B) (τ : A →ₚ[ℂ] ℂ) (σ : B →ₚ[ℂ] ℂ)
    (htrace : ∀ a,σ (e a)=τ a) (u : ℕ → unitary B)
    (hu : ∀ (J : Type) (x : J → B),(∀ j,‖x j‖≤1) → (∀ j,σ (x j)=0) →
      ∀ l : List (Letter J Bool),l≠[] → Valid l →
        Tendsto (fun n => σ (word x signPower (PartialUnitary.ofUnitary (u n)) l)) atTop (𝓝 0)) :
    ∀ (J : Type) (x : J → A),(∀ j,‖x j‖≤1) → (∀ j,τ (x j)=0) →
      ∀ l : List (Letter J Bool),l≠[] → Valid l →
        Tendsto (fun n => τ (word x signPower (PartialUnitary.ofUnitary (pullUnitary e (u n))) l)) atTop (𝓝 0) := by
  intro J x hx hxc l hl hv
  have hh := hu J (e ∘ x) (fun j => by simpa only [Function.comp_apply,StarAlgEquiv.norm_map] using hx j)
    (fun j => (htrace (x j)).trans (hxc j)) l hl hv
  convert hh using 1
  funext n
  rw [←htrace,word_pullUnitary]

section Relative

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M R : VonNeumannAlgebra H) (hRM : R≤M) (e : A ≃⋆ₐ[ℂ] M) (j : R →⋆ₐ[ℂ] A)
    (hj : ∀ q,e (j q)=NormalSubalgebra.inclusion M R hRM q)
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

include hRM hj in
lemma pullUnitary_in_relative_range (u : ℕ → unitary M)
    (hu : ∀ n,((u n:M):H →L[ℂ] H)∈R) :
    (sequenceUnitary τ ω (fun n => pullUnitary e (u n)) : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω)∈
      Set.range ((leftRestricted τ ω).comp (mapSequence j)) := by
  have he : mapSequence j (restrictBoundedUnitary M R u hu)=boundedUnitary (fun n => pullUnitary e (u n)) := by
    ext n
    apply e.injective
    change e (j ⟨u n,hu n⟩)=e (e.symm (u n))
    rw [hj,e.apply_symm_apply]
    rfl
  exact ⟨restrictBoundedUnitary M R u hu,congrArg (leftRestricted τ ω) he⟩

end Relative

end Kadison.TracialSequence

end

end
end

end OAI
