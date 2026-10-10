import OAI.Geometry.SurfaceImmersion.Atlas.RegularCurveCoordinates
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothDoubleAtlas
import OAI.Geometry.SurfaceImmersion.Whitney.DoubleCurveVelocities

namespace OAI

/-! Straight target coordinates for the common image of two actual
regular sheets in a smooth double-locus chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
namespace SmoothDoubleChart
variable {f : M → ProjectionTarget 3}

theorem common_image_coordinates (c : SmoothDoubleChart f)
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f) {t : ℝ}
    (ht : t ∈ c.coord.target)
    (hA : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (c.coord.symm t).val.1))
    (hB : Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (c.coord.symm t).val.2)) :
    ∃ (e : OpenPartialHomeomorph (Base × ℝ) (Fin 3 → ℝ)) (U : Set ℝ),
      IsOpen U ∧ t ∈ U ∧ U ⊆ c.coord.target ∧ ContDiff ℝ ∞ e ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ s ∈ U, (0,s) ∈ e.source ∧
        (EuclideanSpace.equiv (Fin 3) ℝ).symm (e (0,s)) = f (c.coord.symm s).val.1 := by
  let A : ℝ → M := fun s => (c.coord.symm s).val.1
  let B : ℝ → M := fun s => (c.coord.symm s).val.2
  have hAs := c.inverse_left_smooth.contMDiffAt (c.coord.open_target.mem_nhds ht)
  have hBs := c.inverse_right_smooth.contMDiffAt (c.coord.open_target.mem_nhds ht)
  have hEq : f ∘ A =ᶠ[𝓝 t] f ∘ B :=
    Filter.Eventually.of_forall fun s => (c.coord.symm s).property.2
  have hAI := (regular_double_curve_velocities hf hAs hBs hEq (c.inverse_regular t ht) hA hB).1
  have hC : ContDiffOn ℝ ∞ (f ∘ A) c.coord.target :=
    (hf.comp_contMDiffOn c.inverse_left_smooth).contDiffOn
  have hDI : Function.Injective (fderiv ℝ (f ∘ A) t) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp t (hf.mdifferentiable (by simp) (A t))
      (hAs.mdifferentiableAt (by simp))]
    exact hA.comp hAI
  obtain ⟨W,hW,htW,hWT,F,hF,hFC⟩ := CollarVelocity.compact_smooth_extension
    (isCompact_singleton (x := t)) c.coord.open_target (singleton_subset_iff.mpr ht) hC
  have hFe : F =ᶠ[𝓝 t] f ∘ A := hFC.eventuallyEq_of_mem (hW.mem_nhds (htW (by simp)))
  have hFI : Function.Injective (fderiv ℝ F t) := by rw [hFe.fderiv_eq]; exact hDI
  let E := EuclideanSpace.equiv (Fin 3) ℝ
  let C : ℝ → (Fin 3 → ℝ) := E ∘ F
  have hCs : ContDiff ℝ ∞ C := E.contDiff.comp hF
  have hCI : Function.Injective (fderiv ℝ C t) := by
    rw [fderiv_comp t E.differentiableAt (hF.differentiable (by simp) t),E.fderiv]
    exact E.injective.comp hFI
  have hCv : deriv C t ≠ 0 := by
    intro hz
    have he : fderiv ℝ C t 1 = fderiv ℝ C t 0 := by
      rw [fderiv_apply_one_eq_deriv,hz,map_zero]
    have hn := hCI he
    norm_num at hn
  obtain ⟨e,U,hU,htU,hes,hei,haxis⟩ := regular_curve_target_coordinates hCs t hCv
  refine ⟨e,U ∩ W,hU.inter hW,⟨htU,htW (by simp)⟩,
    inter_subset_right.trans hWT,hes,hei,?_⟩
  intro s hs
  refine ⟨(haxis s hs.1).1,?_⟩
  rw [(haxis s hs.1).2]
  change E.symm (E (F s)) = f (A s)
  rw [E.symm_apply_apply]
  exact hFC hs.2

end SmoothDoubleChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
