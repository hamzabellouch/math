import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothAutonomousCurve
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

namespace OAI

/-! # Smooth integral curves on a smooth manifold without boundary -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter Bundle
open scoped Topology Manifold ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]

/-- A smooth vector field pushed into a vector-space chart is smooth. -/
theorem contMDiffAt_chart_velocity
    {φ : M → E} {v : (x : M) → TangentSpace (𝓘(ℝ, E)) x} {x₀ : M}
    (hφ : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ x₀)
    (hv : ContMDiffAt (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨x, v x⟩ : TangentBundle (𝓘(ℝ, E)) M)) x₀) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞
      (fun x => (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ x) (v x)) x₀ := by
  have hϕ := hφ.mfderiv_const (m := ∞) (by simp)
  have hb := ContMDiffAt.clm_apply_of_inCoordinates hϕ hv hφ
  exact (contMDiff_snd_tangentBundle_modelSpace E (𝓘(ℝ, E))).contMDiffAt.comp x₀ hb

/-- Smoothness of a vector field upgrades its integral curves from the
defining first derivative to all finite derivatives. -/
theorem IsMIntegralCurve.contMDiff
    {γ : ℝ → M} {v : (x : M) → TangentSpace (𝓘(ℝ, E)) x}
    (hγ : IsMIntegralCurve (I := 𝓘(ℝ, E)) γ v)
    (hv : ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun x => (⟨x, v x⟩ : TangentBundle (𝓘(ℝ, E)) M))) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) ∞ γ := by
  intro t₀
  let φ := extChartAt (𝓘(ℝ, E)) (γ t₀)
  let V : M → E := fun x => (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ x) (v x)
  let F : E → E := V ∘ φ.symm
  let η : ℝ → E := φ ∘ γ
  have hcont : ContinuousAt γ t₀ := (hγ t₀).continuousAt
  have hφ : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ (γ t₀) :=
    contMDiffAt_extChartAt
  have hV : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ V (γ t₀) :=
    contMDiffAt_chart_velocity hφ (hv (γ t₀))
  have hinv : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ φ.symm (φ (γ t₀)) := by
    simpa only [φ, mfld_simps, contMDiffWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := 𝓘(ℝ, E)) (n := ∞) (γ t₀))
  have hF : ContDiffAt ℝ ∞ F (η t₀) := by
    have hh := hV.comp_of_eq hinv (by simp [φ])
    exact hh.contDiffAt
  have hsource : ∀ᶠ t in 𝓝 t₀, γ t ∈ φ.source :=
    hcont.preimage_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) (γ t₀))
  have hη : ∀ᶠ t in 𝓝 t₀, HasDerivAt η (F (η t)) t := by
    filter_upwards [hsource] with t ht
    have hchart : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)) :=
      (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E)) (by simpa [φ] using ht)).hasMFDerivAt
    have hh : HasFDerivAt η
        ((1 : ℝ →L[ℝ] ℝ).smulRight ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)) (v (γ t)))) t := by
      have raw : HasFDerivAt η
          ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)).comp
            ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))) t :=
        (hchart.comp t (hγ t)).hasFDerivAt
      have heq : (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t))) =
          (1 : ℝ →L[ℝ] ℝ).smulRight
            ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)) (v (γ t))) := by
        ext
        simp
      rw [heq] at raw
      exact raw
    change HasDerivAt η
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (φ.symm (φ (γ t))))
        (v (φ.symm (φ (γ t))))) t
    rw [φ.left_inv ht]
    have hd := hh.hasDerivAt
    change HasDerivAt η ((1 : ℝ) • ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ (γ t)) (v (γ t)))) t at hd
    simpa only [one_smul] using hd
  have hsmooth := contDiffAt_of_autonomous_curve hF hη
  exact (contMDiffAt_iff_target).2 ⟨hcont, hsmooth.contMDiffAt⟩

end PolycyclicRecognition

end

end OAI
