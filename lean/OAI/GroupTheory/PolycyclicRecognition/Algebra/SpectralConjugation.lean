import OAI.GroupTheory.PolycyclicRecognition.Algebra.SemisimpleSquareLog
import Mathlib.Algebra.Star.Module

namespace OAI

/-! # Conjugation compatibility of the spectral logarithm -/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem semisimple_starLinear_ext (S : Module.End ℂ V) (hS : S.IsSemisimple)
    {F G : V →ₗ⋆[ℂ] V}
    (h : ∀ μ x, x ∈ S.eigenspace μ → F x = G x) : F = G := by
  apply sub_eq_zero.mp
  apply LinearMap.ker_eq_top.mp
  apply top_unique
  rw [← hS.iSup_eigenspace_eq_top]
  apply iSup_le
  intro μ x hx
  rw [LinearMap.mem_ker, LinearMap.sub_apply, h μ x hx, sub_self]

theorem semisimpleSpectralOperator_conjugation (S : Module.End ℂ V)
    (hS : S.IsSemisimple) (c : V →ₗ⋆[ℂ] V)
    (hc : ∀ x, c (S x) = S (c x)) (f : ℂ → ℂ)
    (hf : ∀ z, f (star z) = star (f z)) (x : V) :
    c (semisimpleSpectralOperator S hS f x) =
      semisimpleSpectralOperator S hS f (c x) := by
  have he : c.comp (semisimpleSpectralOperator S hS f) =
      (semisimpleSpectralOperator S hS f).comp c := by
    apply semisimple_starLinear_ext S hS
    intro μ y hy
    have hcy : c y ∈ S.eigenspace (star μ) := by
      rw [Module.End.mem_eigenspace_iff, ← hc y,
        Module.End.mem_eigenspace_iff.mp hy, map_smulₛₗ]
      rfl
    change c (semisimpleSpectralOperator S hS f y) =
      semisimpleSpectralOperator S hS f (c y)
    rw [semisimpleSpectralOperator_apply S hS f hy,
      semisimpleSpectralOperator_apply S hS f hcy, map_smulₛₗ, hf]
    rfl
  exact DFunLike.congr_fun he x

end PolycyclicRecognition

end

end OAI
