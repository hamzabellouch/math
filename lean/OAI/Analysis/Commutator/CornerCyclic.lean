import Mathlib
import OAI.Analysis.Commutator.ModuleZeroExtension

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.ReducingRepresentation

open MatrixCornerHilbert

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

lemma range_cyclic_apply (a : A) : σ a ξ∈cyclicSubspace σ.range ξ := by
  exact (orbitSubmodule σ.range ξ).le_topologicalClosure ⟨σ a,Set.mem_range_self a,rfl⟩

theorem restrict_cyclic (K : Submodule ℂ H) [CompleteSpace K]
    (hinv : ∀ a x, x∈K → σ a x∈K) (hξ : ξ∈K)
    (hK : K≤cyclicSubspace σ.range ξ) :
    cyclicSubspace (H := K) (restrict σ K hinv).range (⟨ξ,hξ⟩ : K)=(⊤ : Submodule ℂ K) := by
  let ρ := restrict σ K hinv
  let ζ : K := ⟨ξ,hξ⟩
  let F := cyclicSubspace ρ.range ζ
  change F=⊤
  apply top_unique
  intro z _
  have hz : (z:H)∈cyclicSubspace σ.range ξ := hK z.property
  have hF : IsClosed (F : Set K) := inferInstance
  have hc : IsClosed {x : H | K.orthogonalProjectionOnto x ∈ F} :=
    hF.preimage K.orthogonalProjectionOnto.continuous
  have ho : (orbitSubmodule σ.range ξ : Set H) ⊆ {x : H | K.orthogonalProjectionOnto x ∈ F} := by
    rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    change K.orthogonalProjectionOnto (σ a ξ) ∈ F
    rw [project_intertwines σ K hinv]
    have hζ : K.orthogonalProjectionOnto ξ=ζ := by
      apply Subtype.ext
      exact Submodule.starProjection_eq_self_iff.mpr ζ.property
    rw [hζ]
    exact range_cyclic_apply ρ ζ a
  have he := closure_minimal ho hc hz
  change K.orthogonalProjectionOnto (z:H)∈F at he
  simpa only [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using he

variable {p : A} (hp : IsStarProjection p)

def cornerProjection : H →L[ℂ] fixedSpace (σ p) :=
  (σ p).codRestrict (fixedSpace (σ p)) (by
    intro x
    rw [mem_fixedSpace]
    change (σ p*σ p) x=σ p x
    rw [←map_mul,hp.isIdempotentElem.eq])

@[simp] lemma cornerProjection_fixed (x : fixedSpace (σ p)) :
    cornerProjection σ hp (x:H)=x := by
  apply Subtype.ext
  exact fixed_apply (σ p) x

theorem corner_cyclic (hξ : σ p ξ=ξ) (hcyc : cyclicSubspace σ.range ξ=⊤) :
    cyclicSubspace (H := fixedSpace (σ p)) (corner σ hp).range
      (⟨ξ,(mem_fixedSpace (σ p) ξ).mpr hξ⟩ : fixedSpace (σ p))=⊤ := by
  let ζ : fixedSpace (σ p) := ⟨ξ,(mem_fixedSpace (σ p) ξ).mpr hξ⟩
  let F := cyclicSubspace (corner σ hp).range ζ
  change F=⊤
  apply top_unique
  intro z _
  have hz : (z:H)∈cyclicSubspace σ.range ξ := by rw [hcyc]; trivial
  have hF : IsClosed (F : Set (fixedSpace (σ p))) := inferInstance
  have hc : IsClosed {x : H | cornerProjection σ hp x ∈ F} :=
    hF.preimage (cornerProjection σ hp).continuous
  have ho : (orbitSubmodule σ.range ξ : Set H) ⊆ {x : H | cornerProjection σ hp x ∈ F} := by
    rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    let b : Corner hp := ⟨p*a*p,by rw [←mul_assoc,←mul_assoc,hp.isIdempotentElem.eq],
      by rw [mul_assoc _ p p,hp.isIdempotentElem.eq]⟩
    have he : cornerProjection σ hp (σ a ξ)=corner σ hp b ζ := by
      apply Subtype.ext
      change σ p (σ a ξ)=σ (p*a*p) ξ
      simp only [map_mul,mul_apply_eq_comp]
      rw [hξ]
    change cornerProjection σ hp (σ a ξ)∈F
    rw [he]
    exact range_cyclic_apply (corner σ hp) ζ b
  have he := closure_minimal ho hc hz
  change cornerProjection σ hp (z:H)∈F at he
  simpa only [cornerProjection_fixed] using he

end Kadison.ReducingRepresentation

end

end
end

end OAI
