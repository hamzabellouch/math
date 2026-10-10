import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.Frames
import OAI.AlgebraicGeometry.Seshadri.Intersection.EulerExact

namespace OAI


                                             
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames

lemma finrank_middle_le_of_exact {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K U]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (h : Function.Exact f g) :
    Module.finrank K V ≤ Module.finrank K U + Module.finrank K W := by
  have he := g.finrank_range_add_finrank_ker
  rw [LinearMap.exact_iff.mp h] at he
  have hf := f.finrank_range_le
  have hg := g.range.finrank_le
  omega

variable {X : Scheme.{0}}
local instance : HasExt.{1} X.Modules := schemeHasExt

theorem cohomologyDimension_untwist_bound (p : X ⟶ Spec (CommRingCat.of ℂ))
    {T : ShortComplex X.Modules} (hT : T.ShortExact) (n : ℕ)
    (hf₁ : letI := Module.compHom (cohomology T.X₁ (n+1)) (baseScalars p)
      Module.Finite ℂ (cohomology T.X₁ (n+1)))
    (hf₂ : letI := Module.compHom (cohomology T.X₂ (n+1)) (baseScalars p)
      Module.Finite ℂ (cohomology T.X₂ (n+1)))
    (hf₃ : letI := Module.compHom (cohomology T.X₃ n) (baseScalars p)
      Module.Finite ℂ (cohomology T.X₃ n)) :
    cohomologyDimension p T.X₁ (n+1) ≤
      cohomologyDimension p T.X₃ n + cohomologyDimension p T.X₂ (n+1) := by
  let := sheafComplexLinear p
  let h₁ : Module.Finite ℂ (Ext (O X) T.X₁ (n+1)) := by
    change @Module.Finite ℂ (cohomology T.X₁ (n+1)) _ _ (complexExtModule p T.X₁ (n+1))
    rw [complexExtModule_eq]
    exact hf₁
  let h₂ : Module.Finite ℂ (Ext (O X) T.X₂ (n+1)) := by
    change @Module.Finite ℂ (cohomology T.X₂ (n+1)) _ _ (complexExtModule p T.X₂ (n+1))
    rw [complexExtModule_eq]
    exact hf₂
  let h₃ : Module.Finite ℂ (Ext (O X) T.X₃ n) := by
    change @Module.Finite ℂ (cohomology T.X₃ n) _ _ (complexExtModule p T.X₃ n)
    rw [complexExtModule_eq]
    exact hf₃
  have H := finrank_middle_le_of_exact
    (Cohomology.cohomologyBoundary (K := ℂ) (O X) hT n)
    (Cohomology.cohomologyMap₁ (K := ℂ) (O X) (S := T) (n+1))
    (Cohomology.cohomology_exact₁ (K := ℂ) (O X) hT n)
  change @Module.finrank ℂ (cohomology T.X₁ (n+1)) _ _ (complexExtModule p T.X₁ (n+1)) ≤
    @Module.finrank ℂ (cohomology T.X₃ n) _ _ (complexExtModule p T.X₃ n) +
    @Module.finrank ℂ (cohomology T.X₂ (n+1)) _ _ (complexExtModule p T.X₂ (n+1)) at H
  rw [complexExtModule_eq, complexExtModule_eq, complexExtModule_eq] at H
  exact H
end
end MaximalSeshadri.Geometry

end

end OAI
