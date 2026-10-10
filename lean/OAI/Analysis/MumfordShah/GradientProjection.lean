import Mathlib
import OAI.Analysis.MumfordShah.Model

namespace OAI

/-! MumfordShah gradient projection. -/

noncomputable section
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
namespace MumfordShah
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff

open Set MeasureTheory Topology InnerProductSpace
open scoped ENNReal ContDiff

abbrev PlaneL2 := Lp ℂ 2 (volume : Measure ℂ)

lemma continuous_gradient_of_smooth {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (gradient ψ) := by
  exact (toDual ℝ ℂ).symm.continuous.comp
    (hψ.continuous_fderiv (by norm_num))

lemma compactSupport_gradient {ψ : ℂ → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (gradient ψ) := by
  exact (hψ.fderiv ℝ).comp_left (map_zero (toDual ℝ ℂ).symm)

lemma memLp_gradient_of_test {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) : MemLp (gradient ψ) 2 (volume : Measure ℂ) :=
  (continuous_gradient_of_smooth hψ).memLp_of_hasCompactSupport
    (compactSupport_gradient hψc)

def smoothGradientSpace : Submodule ℝ PlaneL2 where
  carrier := {v | ∃ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
    (v : ℂ → ℂ) =ᵐ[volume] gradient ψ}
  zero_mem' := by
    refine ⟨0, contDiff_const, HasCompactSupport.zero, ?_⟩
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure ℂ))] with x hx
    simp [gradient]
  add_mem' := by
    rintro v w ⟨ψ, hψ, hψc, hv⟩ ⟨ζ, hζ, hζc, hw⟩
    refine ⟨ψ + ζ, hψ.add hζ, hψc.add hζc, ?_⟩
    filter_upwards [Lp.coeFn_add v w, hv, hw] with x hx hvx hwx
    rw [hx, Pi.add_apply, hvx, hwx]
    simp only [gradient,
      fderiv_add (hψ.differentiable (by norm_num) x)
        (hζ.differentiable (by norm_num) x), map_add]
  smul_mem' := by
    rintro c v ⟨ψ, hψ, hψc, hv⟩
    refine ⟨c • ψ, hψ.const_smul c, hψc.smul_left, ?_⟩
    filter_upwards [Lp.coeFn_smul c v, hv] with x hx hvx
    rw [hx, Pi.smul_apply, hvx]
    simp only [gradient,
      fderiv_const_smul (hψ.differentiable (by norm_num) x), map_smul]

def compactGradientClosure : Submodule ℝ PlaneL2 :=
  smoothGradientSpace.topologicalClosure

instance : CompleteSpace compactGradientClosure := by
  unfold compactGradientClosure
  infer_instance

def compactGradientProjection : PlaneL2 →L[ℝ] PlaneL2 :=
  compactGradientClosure.starProjection

def compactJumpField (e : PlaneL2) : PlaneL2 :=
  e - compactGradientProjection e

lemma testGradient_mem_closure {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) :
    (memLp_gradient_of_test hψ hψc).toLp (gradient ψ) ∈ compactGradientClosure := by
  apply smoothGradientSpace.le_topologicalClosure
  exact ⟨ψ, hψ, hψc, (memLp_gradient_of_test hψ hψc).coeFn_toLp⟩

theorem compactJumpField_divergence_free (e : PlaneL2)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    (∫ x : ℂ, inner ℝ (compactJumpField e x) (gradient ψ x)) = 0 := by
  have horth := compactGradientClosure.starProjection_inner_eq_zero e
    ((memLp_gradient_of_test hψ hψc).toLp (gradient ψ)) (testGradient_mem_closure hψ hψc)
  rw [L2.inner_def] at horth
  convert horth using 1
  apply integral_congr_ae
  filter_upwards [(memLp_gradient_of_test hψ hψc).coeFn_toLp] with x hx
  simp only [compactJumpField, compactGradientProjection, hx]

theorem compactJumpField_orthogonal (e : PlaneL2) :
    compactJumpField e ∈ compactGradientClosureᗮ :=
  compactGradientClosure.sub_starProjection_mem_orthogonal e

theorem compactJumpField_memLp (e : PlaneL2) :
    MemLp (compactJumpField e : ℂ → ℂ) 2 (volume : Measure ℂ) :=
  Lp.memLp _

open Set MeasureTheory Metric Topology Filter
open scoped ENNReal ContDiff

end MumfordShah
end

end OAI
