import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportTemplates

namespace OAI

/-! # Strict switching heights beyond a compact probe template -/

noncomputable section
namespace PolycyclicRecognition.SupportDatum

open Set Filter Metric
open scoped Topology

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B]
  (D : PolycyclicRecognition.SupportDatum W I B)

theorem exists_weightSupport_lt_on_open
    {E U : Set W} (hE : IsCompact E) (hne : E.Nonempty)
    (hU : IsOpen U) (hEU : E ⊆ U) (i : I) (hnz : D.weight i ≠ 0) :
    ∃ w ∈ U, D.weightSupport E i < D.weight i w := by
  obtain ⟨x, hx, hsup⟩ := D.exists_weightSupport_point hE hne i
  have hex : ∃ v : W, D.weight i v ≠ 0 := by
    by_contra! h
    apply hnz
    ext v
    exact h v
  obtain ⟨v, hv⟩ := hex
  let u := (D.weight i v)⁻¹ • v
  have hu : D.weight i u = 1 := by simp [u, hv]
  have hc : Continuous (fun a : ℝ => x + a • u) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun a : ℝ => x + a • u) (𝓝 0) (𝓝 x) := by
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  have he : ∀ᶠ a : ℝ in 𝓝 0, x + a • u ∈ U := ht (hU.mem_nhds (hEU hx))
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
  have hin : x + (ε / 2) • u ∈ U := he (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    exact half_lt_self hε)
  refine ⟨_, hin, ?_⟩
  rw [hsup, map_add, map_smul, hu, smul_eq_mul, mul_one]
  linarith

end PolycyclicRecognition.SupportDatum

end

end OAI
