import OAI.Geometry.SurfaceImmersion.Whitney.SmoothArcParameterExtension

namespace OAI

/-! The extended longitudinal parameter has derivative one on the arc,
including its endpoints, and is a submersion there. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem smooth_arc_time_derivative (P : SmoothCompactArc planeModel M)
    {F : M → ℝ} (hF : ContMDiff planeModel 𝓘(ℝ) ∞ F)
    (hFP : ∀ t ∈ Icc P.start P.finish, F (P.curve t) = t)
    {t : ℝ} (ht : t ∈ Icc P.start P.finish) :
    deriv (F ∘ P.curve) t = 1 ∧
      mfderiv planeModel 𝓘(ℝ) F (P.curve t)
        (mfderiv 𝓘(ℝ) planeModel P.curve t 1) = 1 ∧
      Function.Surjective (mfderiv planeModel 𝓘(ℝ) F (P.curve t)) := by
  have hPt := P.smooth.contMDiffAt (P.domain_open.mem_nhds (P.interval_subset ht))
  have hcomp : DifferentiableAt ℝ (F ∘ P.curve) t :=
    ((hF.contMDiffAt.comp t hPt).contDiffAt).differentiableAt (by simp)
  have hwithin : HasDerivWithinAt (F ∘ P.curve) 1 (Icc P.start P.finish) t :=
    (hasDerivWithinAt_id t (Icc P.start P.finish)).congr_of_mem hFP ht
  have hderiv : deriv (F ∘ P.curve) t = 1 :=
    ((uniqueDiffOn_Icc P.start_lt_finish) t ht).eq_deriv (Icc P.start P.finish)
      hcomp.hasDerivAt.hasDerivWithinAt hwithin
  have heval : mfderiv planeModel 𝓘(ℝ) F (P.curve t)
      (mfderiv 𝓘(ℝ) planeModel P.curve t 1) = 1 := by
    rw [← ContinuousLinearMap.comp_apply,← mfderiv_comp t
      (hF.mdifferentiable (by simp) (P.curve t)) (hPt.mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv]
    change fderiv ℝ (F ∘ P.curve) t 1 = 1
    rw [fderiv_apply_one_eq_deriv,hderiv]
  refine ⟨hderiv,heval,?_⟩
  intro y
  change ℝ at y
  refine ⟨y • mfderiv 𝓘(ℝ) planeModel P.curve t 1,?_⟩
  rw [map_smul,heval]
  change y * (1:ℝ) = y
  exact mul_one y

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
