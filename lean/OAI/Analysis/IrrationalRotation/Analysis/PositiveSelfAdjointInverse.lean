import OAI.Analysis.IrrationalRotation.Model.NormalAffiliation
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

namespace OAI

noncomputable section
open scoped ComplexConjugate

namespace Invariant233.PartialInverse

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

theorem dense_range {H : E →ₗ.[𝕜] E} (hH : IsSelfAdjoint H)
    (hker : H.toFun.ker = ⊥) : Dense (LinearMap.range H.toFun : Set E) := by
  have hsa := LinearPMap.isSelfAdjoint_def.mp hH
  have horth : (LinearMap.range H.toFun)ᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hpair (x : H.domain) : inner 𝕜 y (H x) = 0 := by
      exact (inner_eq_zero_symm).mp
        (Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self H.toFun x) hy)
    have hyD : y ∈ H.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists y ⟨0, fun x => by simp [hpair x]⟩
    have hyzero : H.adjoint ⟨y, hyD⟩ = 0 :=
      LinearPMap.adjoint_apply_eq hH.dense_domain _ (fun x => by simp [hpair x])
    have hyH : y ∈ H.domain := by simpa only [hsa] using hyD
    have heq : H.adjoint ⟨y, hyD⟩ = H ⟨y, hyH⟩ := (le_of_eq hsa).2 rfl
    have hyHzero : H ⟨y, hyH⟩ = 0 := heq.symm.trans hyzero
    have hz : (⟨y, hyH⟩ : H.domain) = 0 :=
      (LinearMap.ker_eq_bot.mp hker) (by simpa using hyHzero)
    exact congrArg Subtype.val hz
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]

theorem inverse_dense_domain {H : E →ₗ.[𝕜] E} (hH : IsSelfAdjoint H)
    (hker : H.toFun.ker = ⊥) : Dense (H.inverse.domain : Set E) := by
  rw [LinearPMap.inverse_domain]
  exact dense_range hH hker

omit [CompleteSpace E] in

theorem inverse_mem_domain {H : E →ₗ.[𝕜] E} (hker : H.toFun.ker = ⊥)
    (y : H.inverse.domain) : H.inverse y ∈ H.domain := by
  rw [← LinearPMap.inverse_range (LinearPMap.ker_eq_bot.mpr (LinearMap.ker_eq_bot.mp hker))]
  exact LinearMap.mem_range_self H.inverse.toFun y

omit [CompleteSpace E] in

theorem apply_inverse {H : E →ₗ.[𝕜] E} (hker : H.toFun.ker = ⊥)
    (y : H.inverse.domain) :
    H ⟨H.inverse y, inverse_mem_domain hker y⟩ = (y : E) := by
  have hy : (y : E) ∈ LinearMap.range H.toFun := by
    simpa only [LinearPMap.inverse_domain] using y.property
  obtain ⟨x, hx⟩ := hy
  have hi := LinearPMap.inverse_apply_eq
    (LinearPMap.ker_eq_bot.mpr (LinearMap.ker_eq_bot.mp hker)) hx
  have hsub : (⟨H.inverse y, inverse_mem_domain hker y⟩ : H.domain) = x :=
    Subtype.ext hi
  rw [hsub]
  exact hx

omit [CompleteSpace E] in

theorem inverse_injective {H : E →ₗ.[𝕜] E} (hker : H.toFun.ker = ⊥) :
    Function.Injective H.inverse := by
  intro x y hxy
  have hsub : (⟨H.inverse x, inverse_mem_domain hker x⟩ : H.domain) =
      ⟨H.inverse y, inverse_mem_domain hker y⟩ := Subtype.ext hxy
  apply Subtype.ext
  exact (apply_inverse hker x).symm.trans ((congrArg H hsub).trans (apply_inverse hker y))

omit [CompleteSpace E] in

theorem inverse_formalAdjoint {H : E →ₗ.[𝕜] E}
    (hH : H.IsFormalAdjoint H) (hker : H.toFun.ker = ⊥) :
    H.inverse.IsFormalAdjoint H.inverse := by
  intro x y
  have h := hH ⟨H.inverse x, inverse_mem_domain hker x⟩
    ⟨H.inverse y, inverse_mem_domain hker y⟩
  rw [apply_inverse hker x, apply_inverse hker y] at h
  exact h.symm

theorem inverse_selfAdjoint {H : E →ₗ.[𝕜] E} (hH : IsSelfAdjoint H)
    (hker : H.toFun.ker = ⊥) : IsSelfAdjoint H.inverse := by
  have hsa := LinearPMap.isSelfAdjoint_def.mp hH
  have hd := inverse_dense_domain hH hker
  have hs : H.IsFormalAdjoint H := by
    have h := LinearPMap.adjoint_isFormalAdjoint hH.dense_domain
    rwa [hsa] at h
  have hsym := inverse_formalAdjoint hs hker
  have hpre (y : H.inverse.adjoint.domain) :
      ∃ x : H.domain, H x = (y : E) ∧ (x : E) = H.inverse.adjoint y := by
    have hpair (x : H.domain) :
        inner 𝕜 (y : E) (x : E) = inner 𝕜 (H.inverse.adjoint y) (H x) := by
      let z : H.inverse.domain := ⟨H x, by
        rw [LinearPMap.inverse_domain]
        exact LinearMap.mem_range_self H.toFun x⟩
      have hz : H.inverse z = (x : E) := LinearPMap.inverse_apply_eq
        (LinearPMap.ker_eq_bot.mpr (LinearMap.ker_eq_bot.mp hker)) rfl
      have h := LinearPMap.adjoint_isFormalAdjoint hd y z
      simpa only [hz] using h.symm
    have hw : H.inverse.adjoint y ∈ H.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨y, hpair⟩
    have hwval : H.adjoint ⟨H.inverse.adjoint y, hw⟩ = (y : E) :=
      LinearPMap.adjoint_apply_eq hH.dense_domain _ hpair
    have hwH : H.inverse.adjoint y ∈ H.domain := by simpa only [hsa] using hw
    refine ⟨⟨H.inverse.adjoint y, hwH⟩, ?_, rfl⟩
    exact ((le_of_eq hsa).2 rfl).symm.trans hwval
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx, _⟩ := hpre ⟨y, hy⟩
      rw [LinearPMap.inverse_domain]
      exact ⟨x, hx⟩
    · intro y z hyz
      obtain ⟨x, hx, hxy⟩ := hpre y
      exact hxy.symm.trans (LinearPMap.inverse_apply_eq
        (LinearPMap.ker_eq_bot.mpr (LinearMap.ker_eq_bot.mp hker)) (hx.trans hyz)).symm
  · exact LinearPMap.IsFormalAdjoint.le_adjoint hd hsym

end Invariant233.PartialInverse

namespace Invariant233.PartialInverse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inverse_pairing {H : E →ₗ.[ℂ] E}
    (hH : H.IsFormalAdjoint H) (hker : H.toFun.ker = ⊥)
    (η : H.inverse.domain) (ζ : H.domain) :
    inner ℂ (H.inverse η) (H ζ) = inner ℂ (η : E) (ζ : E) := by
  have h := hH ⟨H.inverse η, inverse_mem_domain hker η⟩ ζ
  rw [apply_inverse hker η] at h
  exact h.symm

theorem inverse_positive {H : E →ₗ.[ℂ] E}
    (hpos : IsPositivePartial H) (hker : H.toFun.ker = ⊥) :
    IsPositivePartial H.inverse := by
  intro y
  have h := hpos ⟨H.inverse y, inverse_mem_domain hker y⟩
  rw [apply_inverse hker y] at h
  exact (inner_re_symm (𝕜 := ℂ) (y : E) (H.inverse y)).trans_ge h

theorem inverse_positive_selfAdjoint [CompleteSpace E] {H : E →ₗ.[ℂ] E}
    (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H) (hinj : Function.Injective H) :
    IsSelfAdjoint H.inverse ∧ IsPositivePartial H.inverse ∧
      Function.Injective H.inverse ∧ Dense (H.inverse.domain : Set E) := by
  have hker : H.toFun.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  exact ⟨inverse_selfAdjoint hH hker, inverse_positive hpos hker,
    inverse_injective hker, inverse_dense_domain hH hker⟩

end Invariant233.PartialInverse

end

end OAI
