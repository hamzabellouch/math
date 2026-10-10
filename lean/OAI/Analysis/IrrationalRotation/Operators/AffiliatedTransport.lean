import OAI.Analysis.IrrationalRotation.Model.AffiliatedTransport
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

noncomputable section

namespace InvariantRotation.AffiliatedTransport

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

@[simp]
theorem mem_domainImage {H : E →ₗ.[𝕜] E} {p : Submodule 𝕜 E} {y : E} :
    y ∈ domainImage H p ↔ ∃ x : H.domain, (x : E) ∈ p ∧ H x = y := by
  simp [domainImage, Submodule.mem_map]

theorem domainImage_invariant
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E) (A B : E →L[𝕜] E)
    (hAp : ∀ x ∈ p, A x ∈ p)
    (hAD : ∀ x ∈ H.domain, A x ∈ H.domain)
    (hAB : ∀ x : H.domain, H ⟨A x, hAD x x.property⟩ = B (H x)) :
    ∀ y ∈ domainImage H p, B y ∈ domainImage H p := by
  intro y hy
  obtain ⟨x, hxp, rfl⟩ := mem_domainImage.mp hy
  exact mem_domainImage.mpr
    ⟨⟨A x, hAD x x.property⟩, hAp x hxp, hAB x⟩

theorem transported_invariant
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E) (A B : E →L[𝕜] E)
    (hAp : ∀ x ∈ p, A x ∈ p)
    (hAD : ∀ x ∈ H.domain, A x ∈ H.domain)
    (hAB : ∀ x : H.domain, H ⟨A x, hAD x x.property⟩ = B (H x)) :
    ∀ y ∈ transported H p, B y ∈ transported H p := by
  have hi : domainImage H p ∈ Module.End.invtSubmodule B.toLinearMap :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
      (domainImage_invariant H p A B hAp hAD hAB)
  exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
    (Submodule.topologicalClosure_mem_invtSubmodule hi)

theorem transported_invariant_of_commutes
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E) (W : E →L[𝕜] E)
    (hWp : ∀ x ∈ p, W x ∈ p)
    (hWD : ∀ x ∈ H.domain, W x ∈ H.domain)
    (hWH : ∀ x : H.domain, H ⟨W x, hWD x x.property⟩ = W (H x)) :
    ∀ y ∈ transported H p, W y ∈ transported H p :=
  transported_invariant H p W W hWp hWD hWH

theorem mem_transported_orthogonal
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E)
    (hH : H.IsFormalAdjoint H) (x : H.domain) (hx : H x ∈ pᗮ) :
    (x : E) ∈ (transported H p)ᗮ := by
  rw [transported, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
  intro y hy
  obtain ⟨z, hzp, rfl⟩ := mem_domainImage.mp hy
  rw [hH z x]
  exact p.inner_right_of_mem_orthogonal hzp hx

theorem inverse_domainImage_le_orthogonal
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E)
    (hH : H.IsFormalAdjoint H) (hker : H.toFun.ker = ⊥) :
    domainImage H.inverse pᗮ ≤ (transported H p)ᗮ := by
  intro y hy
  obtain ⟨z, hzp, rfl⟩ := mem_domainImage.mp hy
  have hz : (z : E) ∈ LinearMap.range H.toFun := by
    simpa only [LinearPMap.inverse_domain] using z.property
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hz
  have hpartialker : H.ker = ⊥ := by simp [LinearPMap.ker, hker]
  rw [LinearPMap.inverse_apply_eq hpartialker hx]
  apply mem_transported_orthogonal H p hH x
  change H.toFun x ∈ pᗮ
  rw [hx]
  exact hzp

theorem inverse_transported_le_orthogonal
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E)
    (hH : H.IsFormalAdjoint H) (hker : H.toFun.ker = ⊥) :
    transported H.inverse pᗮ ≤ (transported H p)ᗮ :=
  Submodule.topologicalClosure_minimal _
    (inverse_domainImage_le_orthogonal H p hH hker)
    (Submodule.isClosed_orthogonal _)

section Complete

variable [CompleteSpace E]

theorem inverse_transported_le_orthogonal_of_selfAdjoint
    (H : E →ₗ.[𝕜] E) (p : Submodule 𝕜 E)
    (hH : IsSelfAdjoint H) (hker : H.toFun.ker = ⊥) :
    transported H.inverse pᗮ ≤ (transported H p)ᗮ := by
  have hs := LinearPMap.adjoint_isFormalAdjoint hH.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hH] at hs
  exact inverse_transported_le_orthogonal H p hs hker

end Complete


variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem transported_projection_mem
    (M : VonNeumannAlgebra F) (H : F →ₗ.[ℂ] F) (p : Submodule ℂ F)
    [p.HasOrthogonalProjection] (hp : p.starProjection ∈ M)
    (hD : ∀ W ∈ M.commutant, ∀ x ∈ H.domain, W x ∈ H.domain)
    (hcomm : ∀ W, ∀ hW : W ∈ M.commutant, ∀ x : H.domain,
      H ⟨W x, hD W hW x x.property⟩ = W (H x)) :
    (transported H p).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro W hW
  rw [Submodule.range_starProjection]
  apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mpr
  have hinv := (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mp hp W hW
  rw [Submodule.range_starProjection] at hinv
  exact transported_invariant_of_commutes H p W
    ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp hinv)
    (hD W hW) (hcomm W hW)


end InvariantRotation.AffiliatedTransport

end

end OAI
