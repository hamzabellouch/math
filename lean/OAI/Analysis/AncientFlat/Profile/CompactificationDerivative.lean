import OAI.Analysis.AncientFlat.Profile.AnnularProfileCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ParabolicAnnular
lemma neg_half_rpow {u : ℝ} (hu : 0≤u) : u^(-(1:ℝ)/2)=(Real.sqrt u)⁻¹ := by
  rw [show -(1:ℝ)/2=-(1/2:ℝ) by ring,Real.rpow_neg hu,←Real.sqrt_eq_rpow]
lemma compactification_deriv (G H : ℝ → ℝ)
    (hG : ContDiffOn ℝ ∞ G (Ici 0))
    (hmatch : ∀ u : ℝ, 0<u → H u=G (u^(-(1:ℝ)/2)))
    {u : ℝ} (hu : 0<u) :
    derivWithin H (Ici 0) u = -deriv G ((Real.sqrt u)⁻¹)/(2*(Real.sqrt u)^3) := by
  have hq : 0<Real.sqrt u := Real.sqrt_pos.mpr hu
  have hGu : DifferentiableAt ℝ G ((Real.sqrt u)⁻¹) :=
    (hG.contDiffAt (Ici_mem_nhds (inv_pos.mpr hq))).differentiableAt (by simp)
  have hi := (Real.hasDerivAt_sqrt hu.ne').inv hq.ne'
  have hd := hGu.hasDerivAt.comp u hi
  have he : H =ᶠ[𝓝 u] fun v => G ((Real.sqrt v)⁻¹) := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    rw [hmatch v hv,neg_half_rpow hv.le]
  have hH := hd.congr_of_eventuallyEq he
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hu),hH.deriv]
  field_simp
end ParabolicAnnular

end

end OAI
