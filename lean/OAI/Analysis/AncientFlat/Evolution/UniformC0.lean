import Mathlib

namespace OAI
noncomputable section
open Set Filter Metric Topology
open scoped ZeroAtInfty
namespace FlatWeighted
variable {T V : Type} [TopologicalSpace T] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma continuous_c0_of_uniform_tails (F : T → C₀(V,ℂ))
    (hc : Continuous (fun p : T × V => F p.1 p.2))
    (ht : ∀ ε : ℝ, 0<ε → ∃ R : ℝ, ∀ t z, R≤‖z‖ → ‖F t z‖≤ε) :
    Continuous F := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt,ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly,
    Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨R,hR⟩ := ht (ε/4) (by positivity)
  let K := closedBall (0:V) R
  have : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:V) R)
  let G : T → C(K,ℂ) := fun s => ⟨fun z => F s z, (F s).continuous.comp continuous_subtype_val⟩
  have hG : Continuous G := ContinuousMap.continuous_of_continuous_uncurry G
    (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hg := (Metric.tendsto_nhds.mp (hG.tendsto t)) (ε/2) (by positivity)
  filter_upwards [hg] with s hs z
  by_cases hz : z∈K
  · exact (ContinuousMap.dist_apply_le_dist (f := G t) (g := G s) ⟨z,hz⟩).trans_lt
      (by simpa only [dist_comm] using hs) |>.trans (by linarith)
  · have hr : R≤‖z‖ := by
      have hz' : ¬‖z‖≤R := by simpa only [K,mem_closedBall,dist_zero_right] using hz
      exact (not_le.mp hz').le
    calc
      dist (F t z) (F s z) = ‖F t z-F s z‖ := dist_eq_norm _ _
      _ ≤ ‖F t z‖+‖F s z‖ := norm_sub_le _ _
      _ ≤ ε/4+ε/4 := add_le_add (hR t z hr) (hR s z hr)
      _ < ε := by linarith
end FlatWeighted

end

end OAI
