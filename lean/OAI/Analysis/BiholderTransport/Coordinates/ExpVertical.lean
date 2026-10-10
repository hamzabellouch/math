import Mathlib
import OAI.Analysis.BiholderTransport.Volume.ExponentialJacobian
import OAI.Analysis.BiholderTransport.Coordinates.SplitLogInjective

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section ExpVertical
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma coordinateEndpointVertical_continuousAt (c : TangentBundle 𝓘(ℝ,Model n) M) :
    ContinuousAt (coordinateEndpointVertical c) c := by
  have hG := coordinateEndpoint_contDiffAt c c (mem_extChartAt_source c)
    (mem_extChartAt_source (riemannianExp c.1 c.2))
  have hG2 : ContDiffAt ℝ 2 (coordinateEndpoint c)
      (extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n)) c c) :=
    hG.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hD := (hG2.fderiv_right (m := 1) (by norm_num)).continuousAt
  have hχ := (contMDiffAt_extChartAt (I := 𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (n := ∞) (x := c)).continuousAt
  exact (hD.comp hχ).clm_comp continuousAt_const

lemma coordinateEndpointVertical_injective {c : TangentBundle 𝓘(ℝ,Model n) M}
    (hc : c.2∈injectivityDomain c.1) : Function.Injective (coordinateEndpointVertical c c) := by
  let X := TangentSpace 𝓘(ℝ,Model n) c.1
  let Y := TangentSpace 𝓘(ℝ,Model n) (riemannianExp c.1 c.2)
  let U := (trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) c.1)
  let V := (trivializationAt (Model n) (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) (riemannianExp c.1 c.2))
  have hU : c.1∈U.baseSet := mem_baseSet_trivializationAt (Model n) _ c.1
  have hV : riemannianExp c.1 c.2∈V.baseSet := mem_baseSet_trivializationAt (Model n) _ _
  have hE := (expJacobian_ne_zero_iff (n := n) c.1 c.2).mp
    (expJacobian_pos_of_injectivityDomain hc).ne'
  apply (injective_iff_map_eq_zero _).mpr
  intro w hw
  let u : X := U.symmL ℝ c.1 w
  have huw : U.continuousLinearMapAt ℝ c.1 u=w := U.continuousLinearMapAt_symmL hU w
  have heq := coordinateEndpointVertical_apply c c (mem_extChartAt_source c)
    (mem_extChartAt_source _) u
  rw [huw,hw] at heq
  have hz : mfderiv 𝓘(ℝ,X) 𝓘(ℝ,Model n) (riemannianExp c.1) c.2 u=0 := by
    have h := congrArg (V.symmL ℝ (riemannianExp c.1 c.2)) heq.symm
    rw [V.symmL_continuousLinearMapAt hV,map_zero] at h
    exact h
  have hu : u=0 := hE (hz.trans (map_zero _).symm)
  rw [←huw,hu,map_zero]

end ExpVertical
end WeakMTWTransport

end

end

end

end OAI
