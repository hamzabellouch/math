import OAI.Analysis.AncientFlat.Evolution.ZeroSourceResponse

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ZeroAtInfty BoundedContinuousFunction Topology
namespace ParametrixVolterra
open FrozenParametrix
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {α β : ℝ}
lemma tendsto_frozen_average (hα : 0<α)
    (A : C(ℝ,V →ᵇ Icc α β)) (f : ℝ →ᵇ C₀(V,ℂ)) :
    Tendsto (fun t : ℝ => t⁻¹ • ∫ r in (0:ℝ)..t, c0Time hα (A r) (t-r) (f r))
      (𝓝[>] 0) (𝓝 (f 0)) := by
  let F (t r : ℝ) := c0Time hα (A (t*r)) (t-t*r) (f (t*r))
  have hF : Continuous F.uncurry := continuous_c0Time_comp hα _ _ _
    (A.continuous.comp (continuous_fst.mul continuous_snd))
    (continuous_fst.sub (continuous_fst.mul continuous_snd))
    (f.continuous.comp (continuous_fst.mul continuous_snd))
  have hc : Continuous (fun t : ℝ => ∫ r in (0:ℝ)..1, F t r) := by
    simp only [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
    exact continuous_parametric_integral_of_continuous hF isCompact_Icc
  have he0 : (∫ r in (0:ℝ)..1, F 0 r)=f 0 := by
    simp [F,c0Time_zero]
  have hh := hc.continuousAt.tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  rw [he0] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have he := intervalIntegral.integral_comp_mul_left
    (fun r => c0Time hα (A r) (t-r) (f r)) (ne_of_gt ht) (a := 0) (b := 1)
  simpa only [mul_zero,mul_one,F] using he
end ParametrixVolterra

end

end OAI
