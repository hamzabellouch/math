import OAI.Geometry.NodalSets.Waves.UniformActualWaveSize

namespace OAI

namespace Yau.Jets
open Filter
open scoped ContDiff Topology
noncomputable section

lemma cutoff_operator_zero_outside (G : Fin 4 → Fin 4 → Coord → ℂ)
    (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ) {N : ℝ} (hN : 0 < N)
    (x : Coord) (hx : 2*N^(-1/3:ℝ) < ‖x‖) :
    smoothSecondOrder G b (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z • u z) x = 0 := by
  have h := cutoff_residual_derivative_zero_outside G b u 0 hN x 0 hx
  have hv := congrArg (fun L : Coord [×0]→L[ℝ] ℂ ↦ L 0) h
  simpa using hv

theorem coefficient_cutoff_operator_eq (beta : ContDiffBump (0:Coord)) :
    ∀ᶠ N : ℝ in atTop, ∀ (G : Fin 4 → Fin 4 → Coord → ℂ)
      (b : Fin 4 → Coord → ℂ) (u : Coord → ℂ),
      smoothSecondOrder (fun i j x ↦ beta x • G i j x) (fun j x ↦ beta x • b j x)
        (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z • u z) =
      smoothSecondOrder G b (fun z ↦ Yau.Waves.scaledCutoff N (0:Coord) z • u z) := by
  have ht : Tendsto (fun N : ℝ ↦ 2*N^(-1/3:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_div,mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul 2
  have he : ∀ᶠ N : ℝ in atTop, 2*N^(-1/3:ℝ) < beta.rIn :=
    ht.eventually (gt_mem_nhds beta.rIn_pos)
  filter_upwards [he,eventually_gt_atTop (0:ℝ)] with N hsmall hN
  intro G b u
  funext x
  by_cases hx : ‖x‖ ≤ 2*N^(-1/3:ℝ)
  · have hbeta : beta x = 1 := beta.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hx.trans hsmall.le)
    simp only [smoothSecondOrder,hbeta,one_smul]
  · rw [cutoff_operator_zero_outside _ _ _ hN x (lt_of_not_ge hx),
      cutoff_operator_zero_outside _ _ _ hN x (lt_of_not_ge hx)]

end
end Yau.Jets

end OAI
