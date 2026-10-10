import OAI.Analysis.CircleDomains.Topology.SphereLevels
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace OAI

/-! The fixed physical sphere metric has locally Lipschitz finite charts.
This follows from the explicit smooth inverse stereographic formula in
Mathlib, including the linear coordinates chosen by the sphere homeomorphism. -/

open Set Function Metric
open scoped Topology NNReal

noncomputable section

namespace CircleDomainRigidity

abbrev RoundAmbient := EuclideanSpace ℝ (Fin 3)

theorem contDiff_roundSphere_finite_chart :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : ℂ => (roundSphereEquiv (z : Sphere) : RoundAmbient)) := by
  classical
  have hlin (W : Submodule ℝ RoundAmbient) (e : ℂ ≃L[ℝ] W) :
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z => (e z : RoundAmbient)) :=
    W.subtypeL.contDiff.comp e.contDiff
  simp only [roundSphereEquiv, onePointEquivSphereOfFinrankEq, Homeomorph.trans_apply,
    Homeomorph.onePointCongr_apply, OnePoint.map_some, onePointHyperplaneHomeoUnitSphere,
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (stereoInvFunAux _ ∘ _)
  apply contDiff_stereoInvFunAux.comp
  exact hlin _ _

attribute [local instance] sphereMetric

theorem finite_sphere_chart_locally_lipschitz (z : ℂ) :
    ∃ L : ℝ≥0, ∃ V ∈ 𝓝 z, LipschitzOnWith L ((↑) : ℂ → Sphere) V := by
  obtain ⟨L, V, hV, hL⟩ :=
    (contDiff_roundSphere_finite_chart.contDiffAt.of_le (show (1 : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) by simp)).exists_lipschitzOnWith
  refine ⟨L, V, hV, ?_⟩
  intro a ha b hb
  exact hL ha hb


theorem finite_sphere_chart_lipschitz_on_compact {K : Set ℂ} (hK : IsCompact K) :
    ∃ L : ℝ≥0, LipschitzOnWith L ((↑) : ℂ → Sphere) K := by
  obtain ⟨R, _, hKR⟩ := hK.isBounded.exists_pos_norm_lt
  let F : ℂ → RoundAmbient := fun z => roundSphereEquiv (z : Sphere)
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F := contDiff_roundSphere_finite_chart
  have hd : Continuous (fun z => ‖fderiv ℝ F z‖₊) :=
    (hF.continuous_fderiv (by simp)).nnnorm
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hd.continuousOn
  have hLip : LipschitzOnWith L F (closedBall (0 : ℂ) R) :=
    Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun _ _ => (hF.differentiable (by simp)).differentiableAt)
      (fun z hz => hL ⟨z, hz, rfl⟩) (convex_closedBall _ _)
  refine ⟨L, ?_⟩
  intro z hz w hw
  apply hLip
  · simpa only [mem_closedBall, dist_zero_right] using (hKR z hz).le
  · simpa only [mem_closedBall, dist_zero_right] using (hKR w hw).le

end CircleDomainRigidity

end

end OAI
