import OAI.Geometry.NodalSets.Elliptic.CorrugationGainStage
import OAI.Geometry.NodalSets.Elliptic.EnvelopeParameterJets
import OAI.Geometry.NodalSets.Persistence.LocalAdmissibilityPersistence

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem envelope_parameter_admissibility
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (S f : Coord → ℝ)
    {K U : Set Coord} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U) (hf : ContDiff ℝ ∞ f)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (ha : sourceDirectionalAdmissibleOn g S K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → sourceDirectionalAdmissibleOn g (S+t • f) K := by
  let p : ℝ × Coord → Coord := fun z ↦ metricGradient g S z.2 + z.1 • metricGradient g f z.2
  let H : ℝ × Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ :=
    fun z ↦ sourceHessian g S z.2 + z.1 • sourceHessian g f z.2
  have he : ∀ᶠ t : ℝ in 𝓝 0, sourceDirectionalAdmissibleOn g (S+t • f) K := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hgx := hg.contDiffAt (hU.mem_nhds (hKU hx))
    have hSx := hS.contDiffAt (hU.mem_nhds (hKU hx))
    have hpx := hp x (hKU hx)
    have hpS : ContinuousAt (metricGradient g S) x :=
      localMetricGradient_continuousAt g S x hgx.continuousAt hSx hpx
    have hpf : ContinuousAt (metricGradient g f) x :=
      localMetricGradient_continuousAt g f x hgx.continuousAt hf.contDiffAt hpx
    have hHS : ContinuousAt (sourceHessian g S) x :=
      localMetricHessian_continuousAt g S x hgx hSx hpx
    have hHf : ContinuousAt (sourceHessian g f) x :=
      localMetricHessian_continuousAt g f x hgx hf.contDiffAt hpx
    have hpc : ContinuousAt p (0,x) := by
      exact (hpS.comp (continuousAt_snd (p := ((0:ℝ),x)) )).fun_add
        (continuousAt_fst.fun_smul (hpf.comp continuousAt_snd))
    have hHc : ContinuousAt H (0,x) := by
      exact (hHS.comp (continuousAt_snd (p := ((0:ℝ),x)) )).fun_add
        (continuousAt_fst.fun_smul (hHf.comp continuousAt_snd))
    obtain ⟨hn,v,hv,hpv,hs⟩ := ha x hx
    have h0 : p (0,x) = metricGradient g S x := by simp [p]
    have hH0 : H (0,x) = sourceHessian g S x := by simp [H]
    have had := admissibility_eventually (fun z : ℝ × Coord ↦ g z.2) H p (0,x)
      (hgx.continuousAt.comp continuousAt_snd) hHc hpc (by simpa [h0] using hpx _ hn)
      v (by simpa [h0] using hpv) hv (by simpa [h0,hH0] using hs)
    have hUn : ∀ᶠ z : ℝ × Coord in 𝓝 (0,x), z.2 ∈ U :=
      continuousAt_snd.preimage_mem_nhds (hU.mem_nhds (hKU hx))
    filter_upwards [had,hUn] with z hz hzU
    obtain ⟨hn,v,hpv,hv,hs⟩ := hz
    obtain ⟨hgp,hgH⟩ := envelope_parameter_jets g S f (hS.contDiffAt (hU.mem_nhds hzU)) hf z.1
    rw [hgp,hgH]
    exact ⟨hn,v,hv,hpv,hs⟩
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ,hδ,fun t ht ↦ hd ?_⟩
  simpa [Real.dist_eq] using ht

end
end Yau.Geometry

end OAI
