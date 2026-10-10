import OAI.GroupTheory.PolycyclicRecognition.Algebra.ChartedInvariantFrame
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RightTranslationInvariant
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ManifoldRelatedBracket

namespace OAI

/-! # Right translations inside a fixed identity chart -/

noncomputable section
namespace PolycyclicRecognition

open Set Function
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem fderiv_fixed_chart_map {f : G → G}
    (hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ f)
    (g₀ : G) {z : E} (hz : z ∈ (extChartAt (𝓘(ℝ, E)) g₀).target)
    (hfz : f ((extChartAt (𝓘(ℝ, E)) g₀).symm z) ∈
      (extChartAt (𝓘(ℝ, E)) g₀).source) :
    fderiv ℝ (extChartAt (𝓘(ℝ, E)) g₀ ∘ f ∘ (extChartAt (𝓘(ℝ, E)) g₀).symm) z =
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) g₀)
        (f ((extChartAt (𝓘(ℝ, E)) g₀).symm z))).comp
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) f ((extChartAt (𝓘(ℝ, E)) g₀).symm z)).comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (extChartAt (𝓘(ℝ, E)) g₀).symm z)) := by
  have hi : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (extChartAt (𝓘(ℝ, E)) g₀).symm z := by
    simpa only [mfld_simps, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm hz
  have ho : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E))
      (extChartAt (𝓘(ℝ, E)) g₀) (f ((extChartAt (𝓘(ℝ, E)) g₀).symm z)) :=
    mdifferentiableAt_extChartAt (by simpa only [mfld_simps] using hfz)
  apply HasFDerivAt.fderiv
  apply (hasMFDerivAt_iff_hasFDerivAt).mp
  exact ho.hasMFDerivAt.comp z
    (((hf _).mdifferentiableAt (by simp)).hasMFDerivAt.comp z hi.hasMFDerivAt)

theorem chart_rightTranslation_related (a : G) (v : E)
    {z : E} (hz : z ∈ (extChartAt (𝓘(ℝ, E)) (1 : G)).target)
    (ha : (extChartAt (𝓘(ℝ, E)) (1 : G)).symm z * a ∈
      (extChartAt (𝓘(ℝ, E)) (1 : G)).source) :
    fderiv ℝ (fun y => extChartAt (𝓘(ℝ, E)) (1 : G)
      ((extChartAt (𝓘(ℝ, E)) (1 : G)).symm y * a)) z
        (chartInvariantFrame (1 : G) z (conjugationDifferentialHom (E := E) a v)) =
      chartInvariantFrame (1 : G)
        (extChartAt (𝓘(ℝ, E)) (1 : G) ((extChartAt (𝓘(ℝ, E)) (1 : G)).symm z * a)) v := by
  let φ := extChartAt (𝓘(ℝ, E)) (1 : G)
  have hf : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (fun h : G => h * a) :=
    contMDiff_mul_right
  have hd := fderiv_fixed_chart_map hf (1 : G) hz ha
  have hD : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm z).IsInvertible := by
    simpa only [φ, mfld_simps, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ, E)) hz
  change fderiv ℝ (φ ∘ (fun h : G => h * a) ∘ φ.symm) z _ = _
  rw [hd]
  change (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (φ.symm z * a))
    ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun h : G => h * a) (φ.symm z))
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm z)
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm z).inverse
          (mulInvariantVectorField (conjugationDifferentialHom (E := E) a v) (φ.symm z))))) = _
  rw [hD.self_apply_inverse, mfderiv_mul_right_invariant]
  have hinv : conjugationDifferentialHom (E := E) a⁻¹ (conjugationDifferentialHom (E := E) a v) = v := by
    change (conjugationDifferentialHom (E := E) a⁻¹ * conjugationDifferentialHom (E := E) a) v = v
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [hinv, chartInvariantFrame_apply]
  exact (chartVectorField_apply_chart (1 : G) (mulInvariantVectorField v) ha).symm

end PolycyclicRecognition

end

end OAI
