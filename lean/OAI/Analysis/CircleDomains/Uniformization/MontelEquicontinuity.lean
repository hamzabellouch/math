import OAI.Analysis.CircleDomains.Topology.MontelCutoffExhaustion
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.MetricSpace.Equicontinuity

namespace OAI

/-! Local holomorphic bounds imply equicontinuity of the cutoff family.
Only finitely many initial cutoffs need individual continuity. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem equicontinuous_cutoffs_of_local_holomorphic_bounds
    {U : Set ℂ} (F : ℕ → ℂ → ℂ) (G : ℕ → C(ℂ, ℂ))
    (hlocal : ∀ x ∈ U, ∃ r > 0, ∃ M > 0, ∀ᶠ n in atTop,
      DifferentiableOn ℂ (F n) (ball x r) ∧
      (∀ z ∈ ball x r, ‖F n z‖ ≤ M) ∧ EqOn (G n) (F n) (ball x r)) :
    Equicontinuous (fun n (x : U) => G n x) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨r,hr,M,hM,hlocal⟩ := hlocal x x.property
  obtain ⟨N,hN⟩ := eventually_atTop.mp hlocal
  have hL : 0 < 2*M/r := div_pos (mul_pos (by norm_num) hM) hr
  have hinit : ∀ᶠ y : U in 𝓝 x, ∀ i : Fin N, dist (G i x) (G i y) < ε := by
    apply eventually_all.mpr
    intro i
    have hg : Tendsto (fun y : U => G i y) (𝓝 x) (𝓝 (G i x)) :=
      ((G i).continuous.comp continuous_subtype_val).tendsto x
    have hc : Tendsto (fun _ : U => G i x) (𝓝 x) (𝓝 (G i x)) := tendsto_const_nhds
    have ht := hc.dist hg
    have ht' : Tendsto (fun y : U => dist (G i x) (G i y)) (𝓝 x) (𝓝 0) := by
      simpa only [dist_self] using ht
    exact ht'.eventually (gt_mem_nhds hε)
  have hδ : 0 < min r (ε/(2*M/r)) := lt_min hr (div_pos hε hL)
  filter_upwards [hinit,ball_mem_nhds x hδ] with y hyinit hy
  intro n
  by_cases hn : n < N
  · exact hyinit ⟨n,hn⟩
  obtain ⟨hd,hb,he⟩ := hN n (Nat.le_of_not_gt hn)
  have hyc : dist (y : ℂ) (x : ℂ) < min r (ε/(2*M/r)) := hy
  have hyr : (y : ℂ) ∈ ball (x : ℂ) r := lt_of_lt_of_le hyc (min_le_left _ _)
  have hxr : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have hm : MapsTo (F n) (ball (x : ℂ) r) (closedBall (F n x) (2*M)) := by
    intro z hz
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hb z hz,hb x hxr])
  rw [he hxr,he hyr,dist_comm]
  calc
    dist (F n y) (F n x) ≤ (2*M/r)*dist (y : ℂ) x :=
      Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hm hyr
    _ < (2*M/r)*(ε/(2*M/r)) :=
      mul_lt_mul_of_pos_left (lt_of_lt_of_le hyc (min_le_right _ _)) hL
    _ = ε := mul_div_cancel₀ ε hL.ne'

end CircleDomainRigidity

end

end OAI
