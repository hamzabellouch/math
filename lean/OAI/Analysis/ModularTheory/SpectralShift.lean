import OAI.Analysis.ModularTheory.SpectralGaussian

namespace OAI

/-! Translation of the modular spectral variable. It preserves the actual
nondegenerate calculus and supplies Gaussian convergence at every frequency
needed by the Fourier-orbit formula. -/

noncomputable section
open Filter
open scoped Topology

namespace BoundedRecovery

def spectralTranslation (s : ℝ) : (BoundedContinuousFunction ℝ ℂ) →⋆ₐ[ℂ]
    BoundedContinuousFunction ℝ ℂ where
  toFun f := f.compContinuous ⟨fun t => t + s, by fun_prop⟩
  map_zero' := by ext; rfl
  map_one' := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl
  commutes' _ := by ext; rfl
  map_star' _ := by ext; rfl

@[simp] lemma spectralTranslation_apply (s : ℝ) (f : BoundedContinuousFunction ℝ ℂ) (t : ℝ) :
    spectralTranslation s f t = f (t + s) := rfl

@[simp] lemma spectralTranslation_cancel (s : ℝ) (f : BoundedContinuousFunction ℝ ℂ) :
    spectralTranslation s (spectralTranslation (-s) f) = f := by
  ext t
  simp only [spectralTranslation_apply, add_neg_cancel_right]

lemma spectralTranslation_compact (s : ℝ) (f : BoundedContinuousFunction ℝ ℂ)
    (hf : HasCompactSupport (f : ℝ → ℂ)) :
    HasCompactSupport (spectralTranslation s f : ℝ → ℂ) := by
  let e : ℝ ≃ₜ ℝ :=
    { toEquiv :=
        { toFun := fun t => t + s
          invFun := fun t => t - s
          left_inv := by intro t; simp
          right_inv := by intro t; simp }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact hf.comp_homeomorph e

namespace RealSpectralCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def shift (D : RealSpectralCalculus H) (s : ℝ) : RealSpectralCalculus H where
  calculus := D.calculus.comp (spectralTranslation s)
  nondegenerate := D.nondegenerate.mono (by
    rintro x ⟨f, hf, v, rfl⟩
    refine ⟨spectralTranslation (-s) f, spectralTranslation_compact (-s) f hf, v, ?_⟩
    simp only [StarAlgHom.comp_apply, spectralTranslation_cancel])

lemma shiftedGaussian_strong (D : RealSpectralCalculus H) (s : ℝ) (v : H) :
    Tendsto (fun n => D.calculus (spectralTranslation s (WeakPureInfiniteness.modularGaussian n)) v)
      atTop (𝓝 v) :=
  WeakPureInfiniteness.modularGaussian_calculus_strong (D.shift s) v

end RealSpectralCalculus
end BoundedRecovery

namespace WeakPureInfiniteness

open BoundedRecovery

def modularShiftedHalfGaussian (n : ℕ) (s : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  (Real.exp (-s / 2) : ℂ) • spectralTranslation s (modularHalfGaussian n)

lemma modularShiftedHalfGaussian_apply (n : ℕ) (s t : ℝ) :
    modularShiftedHalfGaussian n s t =
      (Real.exp (t / 2) : ℂ) * spectralTranslation s (modularGaussian n) t := by
  change (Real.exp (-s / 2) : ℂ) *
    (Real.exp (-(t + s) ^ 2 / (n + 1) + (t + s) / 2) : ℂ) =
      (Real.exp (t / 2) : ℂ) * (Real.exp (-(t + s) ^ 2 / (n + 1)) : ℂ)
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

lemma modularShiftedHalfGaussian_resolvent (n : ℕ) (s : ℝ) :
    modularShiftedHalfGaussian n s * halfResolvent =
      spectralTranslation s (modularGaussian n) * (1 - halfResolvent) := by
  ext t
  change modularShiftedHalfGaussian n s t * halfResolvent t =
    spectralTranslation s (modularGaussian n) t * (1 - halfResolvent t)
  rw [modularShiftedHalfGaussian_apply, mul_comm (Real.exp (t / 2) : ℂ), mul_assoc]
  congr 1
  rw [halfResolvent_apply]
  have h : Real.exp (t / 2) * (Real.exp (t / 2) + 1)⁻¹ =
      1 - (Real.exp (t / 2) + 1)⁻¹ := by
    field_simp
    ring
  exact_mod_cast h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularShiftedHalfGaussian_halfGraph (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph) (s : ℝ) (n : ℕ) :
    D.calculus (modularShiftedHalfGaussian n s) x =
      D.calculus (spectralTranslation s (modularGaussian n)) y :=
  (D.halfGraph_multiplier hxy _ _ (modularShiftedHalfGaussian_resolvent n s)).symm

lemma modularShiftedHalfGaussian_strong (D : RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph) (s : ℝ) :
    Tendsto (fun n => D.calculus (modularShiftedHalfGaussian n s) x) atTop (𝓝 y) := by
  simpa only [modularShiftedHalfGaussian_halfGraph D hxy] using D.shiftedGaussian_strong s y

end WeakPureInfiniteness

end

end OAI
