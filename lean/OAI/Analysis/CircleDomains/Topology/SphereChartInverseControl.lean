import OAI.Analysis.CircleDomains.Sobolev.SphereChartLipschitz

namespace OAI

/-! Local inverse Lipschitz control for the actual fixed finite sphere chart.
The chosen linear coordinates need not be orthonormal. -/

open Set Function Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

theorem linear_stereo_inverse_control (v : RoundAmbient) (hv : ‖v‖ = 1)
    (A : ℂ ≃L[ℝ] (ℝ ∙ v)ᗮ) (z : ℂ) :
    ∃ (L : ℝ≥0) (W : Set RoundAmbient), W ∈ 𝓝 (stereoInvFunAux v (A z : RoundAmbient)) ∧
      ∀ w : ℂ, stereoInvFunAux v (A w : RoundAmbient) ∈ W →
        dist w z ≤ L * dist (stereoInvFunAux v (A w : RoundAmbient))
          (stereoInvFunAux v (A z : RoundAmbient)) := by
  let F : ℂ → RoundAmbient := fun w => stereoInvFunAux v (A w : RoundAmbient)
  let g : RoundAmbient → ℂ := fun x => A.symm (stereoToFun v x)
  have hleft (w : ℂ) : g (F w) = w := by
    change A.symm (stereoToFun v (stereoInvFun hv (A w))) = w
    rw [stereo_right_inv, A.symm_apply_apply]
  have hx : ‖F z‖ = 1 := mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv (A z).property)
  have hneq : innerSL ℝ v (F z) ≠ 1 := by
    intro h
    have he : v = F z := (inner_eq_one_iff_of_norm_eq_one hv hx).mp h
    exact stereoInvFun_ne_north_pole hv (A z) (Subtype.ext he.symm)
  have hopen : IsOpen {x : RoundAmbient | innerSL ℝ v x ≠ 1} :=
    (isClosed_eq (innerSL ℝ v).continuous continuous_const).isOpen_compl
  have hg : ContDiffAt ℝ 1 g (F z) :=
    A.symm.contDiff.contDiffAt.comp (F z)
      ((contDiffOn_stereoToFun (n := 1)).contDiffAt (hopen.mem_nhds hneq))
  obtain ⟨L, W, hW, hL⟩ := hg.exists_lipschitzOnWith
  refine ⟨L, W, hW, fun w hw => ?_⟩
  simpa only [hleft] using hL.dist_le_mul (F w) hw (F z) (mem_of_mem_nhds hW)

theorem finite_sphere_chart_inverse_control (z : ℂ) :
    ∃ (L : ℝ≥0) (W : Set RoundAmbient),
      W ∈ 𝓝 (roundSphereEquiv (z : Sphere) : RoundAmbient) ∧
      ∀ w : ℂ, (roundSphereEquiv (w : Sphere) : RoundAmbient) ∈ W →
        dist w z ≤ L * dist (roundSphereEquiv (w : Sphere) : RoundAmbient)
          (roundSphereEquiv (z : Sphere) : RoundAmbient) := by
  classical
  simp only [roundSphereEquiv, onePointEquivSphereOfFinrankEq, Homeomorph.trans_apply,
    Homeomorph.onePointCongr_apply, OnePoint.map_some, onePointHyperplaneHomeoUnitSphere,
    OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe]
  apply linear_stereo_inverse_control
  simp

end CircleDomainRigidity

end

end OAI
