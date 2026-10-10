import OAI.Probability.ContinuumTransition.ConstructionMasses

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma geometricBudget_tendsto : Tendsto geometricBudget atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma ConstructionData.positions_cauchy {p : ℝ} (C : ConstructionData p) :
    CauchySeq (fun n => (C.stages n).x) := by
  apply cauchySeq_of_le_geometric (1/2) (1/32) (by norm_num)
  intro n
  have hh := (C.transitions n).displacement.le
  rw [dist_comm] at hh
  simpa only [geometricBudget,div_eq_mul_inv,mul_comm,one_mul] using hh

lemma ConstructionData.exists_limit_position {p : ℝ} (C : ConstructionData p) :
    ∃ x : Parameter, Tendsto (fun n => (C.stages n).x) atTop (𝓝 x) ∧
      dist x initialPoint ≤ 1/8 := by
  obtain ⟨x,hx⟩ := cauchySeq_tendsto_of_complete C.positions_cauchy
  refine ⟨x,hx,?_⟩
  apply le_of_tendsto (hx.dist tendsto_const_nhds)
  exact Eventually.of_forall (fun n => (C.stages n).x_near.le)

lemma initial_near_beta {x : Parameter} (hx : dist x initialPoint ≤ 1/8) :
    x.1 ∈ Ioo (1/2:ℝ) (3/2:ℝ) := by
  have hh : |x.1-1| ≤ 1/8 ∧ |x.2-(-3/4)| ≤ 1/8 := by
    simpa only [dist_eq_norm_sub,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
      Real.norm_eq_abs,max_le_iff,initialPoint] using hx
  have hb := hh.1
  rcases abs_le.mp hb with ⟨h₁,h₂⟩
  constructor <;> linarith

lemma initial_near_moderate {x : Parameter} (hx : dist x initialPoint ≤ 1/8) :
    x ∈ moderateBox := initial_ball_moderate (hx.trans (by norm_num : (1:ℝ)/8 ≤ 1/2))

end ContinuumTemperature
end
end

end OAI
